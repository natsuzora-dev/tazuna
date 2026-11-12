import { mkdirSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import type { TraceLine } from "@natsuzora-dev/tazuna";

/** The folder that the check script verifies with `tazuna verify`. */
const traceFolder = join(import.meta.dirname, "../../.traces");

/** Writes the trace as <service>/<name>.jsonl in the trace folder. */
export function writeTrace(service: string, name: string, trace: readonly TraceLine[]): void {
  mkdirSync(join(traceFolder, service), { recursive: true });
  writeFileSync(join(traceFolder, service, `${name}.jsonl`), trace.map((l) => `${JSON.stringify(l)}\n`).join(""));
}
