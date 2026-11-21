import assert from "node:assert/strict";
import { existsSync, readdirSync, readFileSync } from "node:fs";
import { join, relative } from "node:path";
import { after, test } from "node:test";
import { z } from "zod";
import { type Line, scenario } from "../src/data/scenario.generated.ts";
import { type Executed, enabledLines, executeAppended, exploreOf, type Move } from "../src/explore/paths.ts";
import { search } from "../src/explore/search.ts";
import type { LoadedScenario } from "../src/load/scenarios.ts";
import { Halt } from "../src/service/state.ts";
import { checkedRoot, fuzzFoundRoot, runExamples } from "./examples.ts";
import { executeEach, invalidLines, SameWorlds } from "./executed.ts";
import { Lean } from "./lean/lean.ts";

const tazuna = join(import.meta.dirname, "..");

const lean = new Lean();
after(() => lean.close());

const roots = runExamples();

const specs = await Promise.all(
  roots.map(async (root) => ({ name: relative(tazuna, root), spec: await checkedRoot(root) })),
);

for (const { name, spec } of specs) {
  for (const named of spec.scenarios)
    test(`${name}: ${named.service}/${named.name} and every path of up to its explore depth after it execute alike in TS and Lean, continued from the parent path and replayed, and TS and Lean fingerprints take the same worlds as the same`, (t) => {
      const sc = (named.definition as LoadedScenario).scenario;
      const appendedOf = new Map<Executed, readonly Line[]>();
      const worlds = new SameWorlds();
      const both = (appended: readonly Line[], parent?: Executed): Executed => {
        const from =
          parent === undefined || parent.world.violations.length > 0
            ? undefined
            : { executed: parent, appended: appendedOf.get(parent) ?? [] };
        const { executed, difference } = executeEach(lean, spec, sc, appended, worlds, from);
        appendedOf.set(executed, appended);
        assert.equal(
          difference?.other,
          difference?.ts,
          `the executions differ from ${difference?.against} after appending ${JSON.stringify(appended)}`,
        );
        return executed;
      };
      const enabledAfter = enabledLines(spec, sc);
      const invalid = new WeakSet<Move>();
      const next = (path: readonly Move[], executed: Executed): Move[] => {
        const last = path.at(-1);
        const stopped =
          executed.world.halted !== undefined || [...executed.world.services.values()].some((p) => p.halted);
        if (stopped || (last !== undefined && invalid.has(last))) return [];
        let moves: Move[];
        try {
          moves = enabledAfter([...sc.lines, ...(appendedOf.get(executed) ?? [])], executed);
        } catch (error) {
          if (error instanceof Halt) return [];
          throw error;
        }
        const others = invalidLines(spec, sc, executed, moves.flat());
        for (const move of others) invalid.add(move);
        return [...moves, ...others];
      };
      let paths = 0;
      for (const _ of search<Move, Executed>({
        start: { path: [], result: both([]) },
        bound: exploreOf(spec, sc.service).depth,
        step: (parent, path) => both(path.flat(), parent),
        next,
        merge: "none",
      }))
        paths += 1;
      t.diagnostic(`${paths} paths`);
    });
}

const specOf = new Map(specs.map(({ name, spec }) => [name, spec]));

/**
 * A fixture that npm run fuzz writes: the scenario with the lines it appended, and how many lines the differing
 * execution continued from, or null when it replayed every line.
 */
const fuzzFoundFixture = z.strictObject({
  spec: z.string(),
  scenario: z.unknown(),
  from: z.int().nonnegative().nullable(),
});

const fuzzFound = existsSync(fuzzFoundRoot) ? readdirSync(fuzzFoundRoot).filter((f) => f.endsWith(".json")) : [];

for (const file of fuzzFound.sort())
  test(`fuzz-found/${file} executes alike in TS with and without the evaluation cache, continued from its first lines when it was, and in Lean`, async () => {
    const found = fuzzFoundFixture.parse(JSON.parse(readFileSync(join(fuzzFoundRoot, file), "utf8")));
    const spec = specOf.get(found.spec) ?? (await checkedRoot(join(tazuna, found.spec)));
    const full = scenario.parse(found.scenario);
    const from = found.from ?? full.lines.length;
    const sc = { ...full, lines: full.lines.slice(0, from) };
    const parent = found.from === null ? undefined : { executed: executeAppended(spec, sc, []), appended: [] };
    const { difference } = executeEach(lean, spec, sc, full.lines.slice(from), new SameWorlds(), parent);
    assert.equal(difference?.other, difference?.ts, `the execution differs from ${difference?.against}`);
  });
