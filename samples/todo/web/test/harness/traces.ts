import { mkdirSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import type { TraceLine } from "@natsuzora-dev/tazuna";

/** The folder that the check script verifies with `tazuna verify`. */
const traceFolder = join(import.meta.dirname, "../../.traces");

/** Returns a function that gives a line without an id of the app the id `<name>#<n>`, counting the lines per name. */
export function lineIds(): (name: string) => string {
  const counts = new Map<string, number>();
  return (name) => {
    const n = (counts.get(name) ?? 0) + 1;
    counts.set(name, n);
    return `${name}#${n}`;
  };
}

/** Writes the trace as <service>/<name>.jsonl in the trace folder. */
export function writeTrace(service: string, name: string, trace: readonly TraceLine[]): void {
  mkdirSync(join(traceFolder, service), { recursive: true });
  writeFileSync(join(traceFolder, service, `${name}.jsonl`), trace.map((l) => `${JSON.stringify(l)}\n`).join(""));
}
