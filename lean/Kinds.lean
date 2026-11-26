import Tazuna.Cli.Explain

open Lean (Json)

/-- The fields of a printed line that `explain` does not name for its kind, or why the line names no kind. -/
def unexplained (text : String) : List String :=
  match Json.parse text with
  | .error e => [s!"not JSON: {e}"]
  | .ok j => match j.getObjValAs? String "kind" with
    | .error _ => ["no kind"]
    | .ok name => match Tazuna.Kind.all.find? (·.name == name) with
      | none => [s!"no kind is named {name}"]
      | some k =>
        let known := k.explanation.fields.map (·.key)
        let keys : List String := match j.getObj? with
          | .ok kvs => kvs.keys
          | .error _ => []
        (keys.filter fun key => key != "kind" && !known.contains key).map (s!"{name} has a field {·} explain does not name")

/-- With no arguments, prints the name of every output kind test/e2e has a case of, one per line. With `--lines` and
files, checks that each line of each file names a kind and carries only fields `explain` names for it. -/
def main : List String → IO UInt32
  | [] => do
    (Tazuna.Kind.all.filter (·.e2e)).forM fun k => IO.println k.name
    return 0
  | "--lines" :: files => do
    let mut ok := true
    for file in files do
      for text in (← IO.FS.readFile file).splitOn "\n" do
        if text.isEmpty then continue
        for problem in unexplained text do
          IO.eprintln s!"{file}: {problem}"
          ok := false
    return if ok then 0 else 1
  | _ => do
    IO.eprintln "usage: kinds [--lines <file>...]"
    return 3
