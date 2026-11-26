//// The launcher behind `gleam run -m tazuna -- <command> <root> [...]`. It
//// converts `src/<root>.gleam` and the modules it imports from `src/`,
//// writes the IR to `build/tazuna/<root>.ir.json`, and runs the engine with
//// the arguments as given plus `--ir <path>`, passing on its output and exit
//// code. The engine owns what the arguments mean; the launcher reads only
//// the root, and passes `explain` on as it is.

import glance
import gleam/io
import gleam/list
import gleam/result
import gleam/string
import simplifile
import tazuna/internal/convert.{type Source, Source}
import tazuna/internal/json
import tazuna/internal/kind

pub fn main() -> Nil {
  exit(run(argv()))
}

fn run(args: List(String)) -> Int {
  case getenv("TAZUNA_ENGINE") {
    Error(_) ->
      fail(
        kind.System,
        "Set TAZUNA_ENGINE to the path of the tazuna-engine executable.",
      )
    Ok(engine) ->
      case args {
        // explain reads no spec, so there is nothing to convert.
        ["explain", ..] -> run_engine(engine, args)
        [_command, root, ..] -> check(engine, args, root)
        // No root: the engine prints its version or its usage.
        _ -> run_engine(engine, args)
      }
  }
}

fn check(engine: String, args: List(String), root: String) -> Int {
  let path = "src/" <> root <> ".gleam"
  case simplifile.is_file(path) {
    Ok(True) ->
      case
        convert.convert(sources([root], []), root)
        |> result.try(fn(program) {
          case convert.root_findings(program) {
            [] -> Ok(program)
            findings -> Error(findings)
          }
        })
      {
        Error(findings) -> {
          list.each(findings, fn(f) { io.println(convert.finding_line(f)) })
          kind.exit_code(list.map(findings, fn(f) { f.kind }))
        }
        Ok(program) -> {
          let ir = "build/tazuna/" <> root <> ".ir.json"
          case write(ir, convert.ir_text(program)) {
            Ok(Nil) -> run_engine(engine, list.append(args, ["--ir", ir]))
            Error(e) ->
              fail(
                kind.System,
                "could not write " <> ir <> ": " <> simplifile.describe_error(e),
              )
          }
        }
      }
    _ -> fail(kind.Arguments, "There is no root module " <> path <> ".")
  }
}

/// The modules in `queue` and those they import, transitively, that `src/`
/// holds. The converter reports any other import a spec uses.
fn sources(queue: List(String), done: List(Source)) -> List(Source) {
  case queue {
    [] -> list.reverse(done)
    [module, ..rest] -> {
      let path = "src/" <> module <> ".gleam"
      case list.any(done, fn(s) { s.module == module }), simplifile.read(path) {
        False, Ok(text) ->
          sources(list.append(rest, imports(text)), [
            Source(module, path, text),
            ..done
          ])
        _, _ -> sources(rest, done)
      }
    }
  }
}

/// A module glance cannot parse imports nothing here; the converter reports
/// the parse error.
fn imports(text: String) -> List(String) {
  case glance.module(text) {
    Ok(m) -> list.map(m.imports, fn(i) { i.definition.module })
    Error(_) -> []
  }
}

fn write(path: String, text: String) -> Result(Nil, simplifile.FileError) {
  let parts = string.split(path, "/")
  let dir = list.take(parts, list.length(parts) - 1) |> string.join("/")
  case simplifile.create_directory_all(dir) {
    Ok(Nil) -> simplifile.write(path, text)
    Error(e) -> Error(e)
  }
}

fn run_engine(engine: String, args: List(String)) -> Int {
  case spawn(engine, args) {
    Ok(code) -> code
    Error(message) ->
      fail(kind.System, "could not run " <> engine <> ": " <> message)
  }
}

/// Prints the launcher's own line of the kind; the exit code it gives.
fn fail(usage: kind.Usage, message: String) -> Int {
  let k = kind.Usage(usage)
  io.println(
    json.encode(
      json.Object([
        #("kind", json.Str(kind.name(k))),
        #("message", json.Str(message)),
      ]),
    ),
  )
  kind.exit_code([k])
}

@external(erlang, "tazuna_launch_ffi", "argv")
@external(javascript, "./launch_ffi.mjs", "argv")
fn argv() -> List(String)

@external(erlang, "tazuna_launch_ffi", "getenv")
@external(javascript, "./launch_ffi.mjs", "getenv")
fn getenv(name: String) -> Result(String, Nil)

/// Runs the executable with its standard output passed through line by line
/// and its standard error inherited, and returns its exit code.
@external(erlang, "tazuna_launch_ffi", "spawn")
@external(javascript, "./launch_ffi.mjs", "spawn")
fn spawn(path: String, args: List(String)) -> Result(Int, String)

@external(erlang, "tazuna_launch_ffi", "exit")
@external(javascript, "./launch_ffi.mjs", "exit")
fn exit(code: Int) -> Nil
