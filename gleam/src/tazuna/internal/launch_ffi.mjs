import { spawnSync } from "node:child_process";
import { constants } from "node:os";
import { Error, Ok, toList } from "../../gleam.mjs";

export function argv() {
  return toList(process.argv.slice(2));
}

export function getenv(name) {
  const value = process.env[name];
  return value === undefined ? new Error(undefined) : new Ok(value);
}

export function spawn(path, args) {
  const result = spawnSync(path, args.toArray(), { stdio: "inherit" });
  if (result.error) return new Error(result.error.message);
  if (result.status !== null) return new Ok(result.status);
  // Killed by a signal: the shell's convention.
  return new Ok(128 + (constants.signals[result.signal] ?? 0));
}

// process.exit could drop output still queued for a pipe; setting the code lets
// Node drain it and exit once main returns.
export function exit(code) {
  process.exitCode = code;
}
