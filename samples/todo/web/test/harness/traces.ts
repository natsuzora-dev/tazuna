import { mkdirSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";
import type { LogLine } from "@natsuzora-dev/tazuna/verify";

/** The folder that the check script verifies with `tazuna verify`. */
const traceFolder = join(import.meta.dirname, "../../.traces");

/** Writes the trace at `file` in the trace folder: a run's runFile, or <service>/<name>.jsonl of an external service. */
export function writeTrace(file: string, trace: readonly LogLine[]): void {
  const path = join(traceFolder, file);
  mkdirSync(dirname(path), { recursive: true });
  writeFileSync(path, trace.map((l) => `${JSON.stringify(l)}\n`).join(""));
}
