import { spawnSync } from "node:child_process";
import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";
import { constants } from "node:os";
import { fileURLToPath } from "node:url";
import { gunzipSync } from "node:zlib";
import { BitArray, Error, Ok, toList } from "../../gleam.mjs";

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

export function platform() {
  return `${process.platform}-${process.arch}`;
}

export function download(url, done) {
  get(url).then(done);
}

async function get(url) {
  try {
    if (url.startsWith("file://")) {
      return new Ok(new BitArray(readFileSync(fileURLToPath(url))));
    }
    const response = await fetch(url, { headers: { "user-agent": "tazuna" } });
    if (!response.ok) return new Error(`HTTP status ${response.status}`);
    return new Ok(new BitArray(new Uint8Array(await response.arrayBuffer())));
  } catch (e) {
    return new Error(e.message);
  }
}

export function sha256(bits) {
  return createHash("sha256").update(bits.rawBuffer).digest("hex");
}

export function gunzip(bits) {
  try {
    return new Ok(new BitArray(gunzipSync(bits.rawBuffer)));
  } catch (e) {
    return new Error(e.message);
  }
}

export function pid() {
  return process.pid;
}
