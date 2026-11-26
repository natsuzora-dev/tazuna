//// Where the engine is. `TAZUNA_ENGINE` names one, such as an engine built
//// from lean/. Otherwise the engine and z3 for this platform come from the
//// release of the package's version on first run, each checked against the
//// SHA-256 the package pins, and stay in the user cache directory for later
//// runs. z3 goes beside the engine, where the engine looks for it.

import gleam/bool
import gleam/io
import gleam/list
import gleam/result
import gleam/string
import simplifile
import tazuna/internal/engine_pin.{type Asset}

/// The engine's path, or why there is none.
pub fn locate(done: fn(Result(String, String)) -> Nil) -> Nil {
  case getenv("TAZUNA_ENGINE") {
    Ok(path) -> done(Ok(path))
    Error(Nil) -> fetch(platform(), done)
  }
}

fn fetch(platform: String, done: fn(Result(String, String)) -> Nil) -> Nil {
  case
    list.find(engine_pin.pins, fn(pin) { pin.platform == platform }),
    cache_root(platform)
  {
    Error(Nil), _ ->
      done(Error(
        "tazuna "
        <> engine_pin.version
        <> " has no engine for "
        <> platform
        <> "; set TAZUNA_ENGINE to the path of a tazuna-engine executable",
      ))
    _, Error(Nil) ->
      done(Error(
        "there is no user cache directory to keep the engine in (HOME, or LOCALAPPDATA on Windows, is not set)",
      ))
    Ok(pin), Ok(root) -> {
      let dir = root <> "/tazuna/" <> engine_pin.version <> "/" <> platform
      let exe = case platform {
        "win32-" <> _ -> ".exe"
        _ -> ""
      }
      use z3 <- install(dir, "z3" <> exe, pin.z3)
      case z3 {
        Ok(_) -> install(dir, "tazuna-engine" <> exe, pin.engine, done)
        Error(e) -> done(Error(e))
      }
    }
  }
}

/// The user cache directory, as Go's os.UserCacheDir finds it.
fn cache_root(platform: String) -> Result(String, Nil) {
  let home = fn(under) { result.map(getenv("HOME"), fn(h) { h <> under }) }
  case platform, getenv("XDG_CACHE_HOME") {
    "darwin-" <> _, _ -> home("/Library/Caches")
    "win32-" <> _, _ -> getenv("LOCALAPPDATA")
    _, Ok(dir) if dir != "" -> Ok(dir)
    _, _ -> home("/.cache")
  }
}

/// A cached file is there only once it was checked: it is written under
/// another name and renamed, so a run cut short leaves no file to trust.
fn install(
  dir: String,
  name: String,
  asset: Asset,
  done: fn(Result(String, String)) -> Nil,
) -> Nil {
  let path = dir <> "/" <> name
  use <- bool.lazy_guard(simplifile.is_file(path) == Ok(True), fn() {
    done(Ok(path))
  })
  let url = engine_pin.release <> "/" <> asset.name
  io.println_error("tazuna: fetching " <> url)
  use got <- download(url)
  done({
    use gz <- result.try(
      result.map_error(got, fn(e) { "could not download " <> url <> ": " <> e }),
    )
    let sha = sha256(gz)
    use <- bool.guard(
      sha != asset.sha256,
      Error(
        url
        <> " has SHA-256 "
        <> sha
        <> ", not the "
        <> asset.sha256
        <> " this package pins",
      ),
    )
    use bits <- result.try(
      result.map_error(gunzip(gz), fn(e) { url <> " does not unzip: " <> e }),
    )
    write_executable(dir, path, bits)
  })
}

fn write_executable(
  dir: String,
  path: String,
  bits: BitArray,
) -> Result(String, String) {
  let part = path <> ".part" <> string.inspect(pid())
  {
    use _ <- result.try(simplifile.create_directory_all(dir))
    use _ <- result.try(simplifile.write_bits(part, bits))
    use _ <- result.try(simplifile.set_permissions_octal(part, 0o755))
    simplifile.rename(part, path)
  }
  |> result.map(fn(_) { path })
  |> result.map_error(fn(e) {
    "could not write " <> path <> ": " <> simplifile.describe_error(e)
  })
}

@external(erlang, "tazuna_launch_ffi", "getenv")
@external(javascript, "./launch_ffi.mjs", "getenv")
fn getenv(name: String) -> Result(String, Nil)

/// `<os>-<arch>` as Node names them, such as `darwin-arm64`.
@external(erlang, "tazuna_launch_ffi", "platform")
@external(javascript, "./launch_ffi.mjs", "platform")
fn platform() -> String

/// Gets an https:// URL, or reads a file:// URL.
@external(erlang, "tazuna_launch_ffi", "download")
@external(javascript, "./launch_ffi.mjs", "download")
fn download(url: String, done: fn(Result(BitArray, String)) -> Nil) -> Nil

/// In lowercase hex.
@external(erlang, "tazuna_launch_ffi", "sha256")
@external(javascript, "./launch_ffi.mjs", "sha256")
fn sha256(bits: BitArray) -> String

@external(erlang, "tazuna_launch_ffi", "gunzip")
@external(javascript, "./launch_ffi.mjs", "gunzip")
fn gunzip(bits: BitArray) -> Result(BitArray, String)

@external(erlang, "tazuna_launch_ffi", "pid")
@external(javascript, "./launch_ffi.mjs", "pid")
fn pid() -> Int
