import assert from "node:assert/strict";
import { existsSync, readdirSync, readFileSync } from "node:fs";
import { join, relative } from "node:path";
import { after, test } from "node:test";
import { type Line, scenario } from "../src/data/scenario.generated.ts";
import {
  type Executed,
  enabledLines,
  executeAppended,
  type Move,
  seenLines,
  valuesPerPayload,
} from "../src/explore/paths.ts";
import { search } from "../src/explore/search.ts";
import type { LoadedScenario } from "../src/load/scenarios.ts";
import { Halt } from "../src/service/state.ts";
import { checkedRoot, depth, fuzzFoundRoot, runExamples } from "./examples.ts";
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
  const seen = seenLines(spec);
  for (const named of spec.scenarios)
    test(`${name}: ${named.service}/${named.name} and every path of up to ${depth} moves after it execute alike in TS and Lean, continued from the parent path and replayed, and TS and Lean fingerprints take the same worlds as the same`, (t) => {
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
      const enabledAfter = enabledLines(spec, sc, seen, valuesPerPayload);
      const invalid = new WeakSet<Move>();
      const made = new Map<Executed, Map<Move, Executed>>();
      const next = (path: readonly Move[], executed: Executed): Move[] => {
        const last = path.at(-1);
        const stopped =
          executed.world.halted !== undefined || [...executed.world.services.values()].some((p) => p.halted);
        if (stopped || (last !== undefined && invalid.has(last))) return [];
        const appended = appendedOf.get(executed) ?? [];
        let moves: Move[];
        try {
          moves = enabledAfter([...sc.lines, ...appended], executed);
        } catch (error) {
          if (error instanceof Halt) return [];
          throw error;
        }
        const children = new Map(moves.map((move) => [move, both([...appended, ...move], executed)]));
        made.set(executed, children);
        const others = invalidLines(spec, sc, executed, moves.flat());
        for (const move of others) invalid.add(move);
        return [...children.keys(), ...others];
      };
      let paths = 0;
      for (const _ of search<Move, Executed>({
        start: { path: [], result: both([]) },
        bound: depth,
        step: (parent, move) => {
          const children = made.get(parent);
          const executed = children?.get(move);
          if (children === undefined || executed === undefined)
            return both([...(appendedOf.get(parent) ?? []), ...move], parent);
          children.delete(move);
          if (children.size === 0) made.delete(parent);
          return executed;
        },
        next,
        merge: "none",
      }))
        paths += 1;
      t.diagnostic(`${paths} paths`);
    });
}

const specOf = new Map(specs.map(({ name, spec }) => [name, spec]));

const fuzzFound = existsSync(fuzzFoundRoot) ? readdirSync(fuzzFoundRoot).filter((f) => f.endsWith(".json")) : [];

for (const file of fuzzFound.sort())
  test(`fuzz-found/${file} executes alike in TS with and without the evaluation cache, continued from its first lines, and in Lean`, async () => {
    const found = JSON.parse(readFileSync(join(fuzzFoundRoot, file), "utf8")) as {
      spec: string;
      scenario: unknown;
      from: number;
    };
    const spec = specOf.get(found.spec) ?? (await checkedRoot(join(tazuna, found.spec)));
    const full = scenario.parse(found.scenario);
    const sc = { ...full, lines: full.lines.slice(0, found.from) };
    const parent = { executed: executeAppended(spec, sc, []), appended: [] };
    const { difference } = executeEach(lean, spec, sc, full.lines.slice(found.from), new SameWorlds(), parent);
    assert.equal(difference?.other, difference?.ts, `the execution differs from ${difference?.against}`);
  });
