import { existsSync, mkdirSync, readdirSync, rmSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import type { CheckedSpec } from "../check/spec.ts";
import { InternalError } from "../data/internalError.ts";
import type { Location } from "../data/violation.ts";
import { placeOf } from "../load/found.ts";
import { solve } from "../z3/solve.ts";
import { ask } from "./engine.ts";
import type { Generation, TargetOutcome } from "./protocol.generated.ts";

/** What generate found of a target, at the definition that the target is a part of. */
export type GenerateLine = TargetOutcome & { readonly location: Location };

/** generate's result: the engine asks Z3 round by round, each round given every output so far, until it has the result. */
async function generationOf(spec: CheckedSpec, depth: number | undefined): Promise<Generation> {
  const answers: string[] = [];
  for (;;) {
    const [round] = ask("generate", [
      { structure: spec.structure, ...(depth === undefined ? {} : { depth }), answers },
    ]);
    if (round === undefined) throw new InternalError("the engine gave no round of generate");
    if (round.result !== null) return round.result;
    if (round.scripts.length === 0) throw new InternalError("the engine asked no script and gave no result");
    answers.push(...(await solve(round.scripts)));
  }
}

/**
 * Writes each input that generate keeps to `<out>/<service>/<name>.jsonl`, one trace line per line, and removes the other
 * files of those service folders, and returns what generate found of each target and the paths written and removed.
 */
export async function generateSpec(
  spec: CheckedSpec,
  out: string,
  depth: number | undefined,
): Promise<{ readonly lines: readonly GenerateLine[]; readonly written: string[]; readonly removed: string[] }> {
  const generation = await generationOf(spec, depth);
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
