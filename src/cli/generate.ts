import { existsSync, mkdirSync, readdirSync, rmSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import type { ConvertedSpec } from "../check/spec.ts";
import type { Location } from "../data/violation.ts";
import { placeOf } from "../load/found.ts";
import { solve } from "../z3/solve.ts";
import { converse } from "./engine.ts";
import type { TargetOutcome } from "./protocol.generated.ts";

/** What generate found of a target, at the definition that the target is a part of. */
export type GenerateLine = TargetOutcome & { readonly location: Location };

/**
 * Writes each input that generate keeps to `<out>/<service>/<name>.jsonl`, one trace line per line, and removes the other
 * files of those service folders, and returns what generate found of each target and the paths written and removed.
 */
export async function generateSpec(
  spec: ConvertedSpec,
  out: string,
  depth: number | undefined,
): Promise<{ readonly lines: readonly GenerateLine[]; readonly written: string[]; readonly removed: string[] }> {
  const { result: generation } = await converse(
    "generate",
    { structure: spec.structure, ...(depth === undefined ? {} : { depth }) },
    solve,
  );
  const written: string[] = [];
  for (const input of generation.inputs) {
    const folder = join(out, input.service);
    mkdirSync(folder, { recursive: true });
    const path = join(folder, `${input.name}.jsonl`);
    writeFileSync(path, input.lines.map((l) => `${JSON.stringify(l)}\n`).join(""));
    written.push(path);
  }
  const removed: string[] = [];
  for (const service of spec.structure.services.filter((s) => !s.external)) {
    const folder = join(out, service.name);
    if (!existsSync(folder)) continue;
    for (const entry of readdirSync(folder, { withFileTypes: true, recursive: true }).filter((e) => e.isFile())) {
      const path = join(entry.parentPath, entry.name);
      if (!written.includes(path)) {
        rmSync(path);
        removed.push(path);
      }
    }
  }
  const lines = generation.targets.map((t) => {
    const { file, line } = placeOf(spec, t.target.definition);
    return { ...t, location: { file, line } };
  });
  return { lines, written, removed };
}
