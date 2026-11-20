import { mkdirSync, writeFileSync } from "node:fs";
import { join, relative } from "node:path";
import { parseArgs } from "node:util";
import fc from "fast-check";
import { z } from "zod";
import { date, datetime } from "../src/data/datetime.ts";
import type { Line, Scenario, Template } from "../src/data/scenario.generated.ts";
import type { Answer } from "../src/data/trace.generated.ts";
import type { Shape } from "../src/data/values.ts";
import { chartOf } from "../src/dsl/chart.ts";
import type { AnyCommand, AnyEvent, AnyQuery } from "../src/dsl/definition.ts";
import {
  type Executed,
  enabledLines,
  executeAppended,
  type Move,
  seenLines,
  valuesPerPayload,
} from "../src/explore/paths.ts";
import type { Spec } from "../src/load/load.ts";
import type { LoadedScenario } from "../src/load/scenarios.ts";
import { Halt } from "../src/service/state.ts";
import { checkedRoot, fuzzFoundRoot, runExamples } from "../test/examples.ts";
import { type Difference, executeEach, invalidLines } from "../test/executed.ts";
import { Lean } from "../test/lean/lean.ts";

const usage = "npm run fuzz -- [--seed <integer>] [--runs <count>] [--depth <moves>]";
const { values: options } = parseArgs({
  options: {
    seed: { type: "string" },
    runs: { type: "string", default: "100" },
    depth: { type: "string", default: "8" },
  },
});
const integer = (text: string, name: string): number => {
  const n = Number(text);
  if (!Number.isSafeInteger(n)) throw new Error(`--${name} takes an integer: ${usage}`);
  return n;
};
const seed = options.seed === undefined ? Date.now() % 2 ** 31 : integer(options.seed, "seed");
const runs = integer(options.runs, "runs");
const depth = integer(options.depth, "depth");

const tazuna = join(import.meta.dirname, "..");
const roots = [join(tazuna, "samples/todo/spec"), ...runExamples()];

const stopped = ({ world }: Executed) =>
  world.halted !== undefined || [...world.services.values()].some((p) => p.halted !== undefined);

interface Case {
  readonly spec: Spec;
  /** The spec's root, relative to the repository. */
  readonly root: string;
  readonly sc: Scenario;
  readonly words: readonly string[];
  readonly enabledAfter: (lines: readonly Line[], executed: Executed) => Move[];
}

const cases: Case[] = (
  await Promise.all(
    roots.map(async (root) => {
      const spec = await checkedRoot(root);
      const seen = seenLines(spec);
      return spec.scenarios.flatMap(({ definition }): Case[] => {
        const sc = (definition as LoadedScenario).scenario;
        // run.diff covers a scenario that stops by itself, and no move comes after it.
        if (stopped(executeAppended(spec, sc, []))) return [];
        return [
          {
            spec,
            root: relative(tazuna, root),
            sc,
            words: seen.words,
            enabledAfter: enabledLines(spec, sc, seen, valuesPerPayload),
          },
        ];
      });
    }),
  )
).flat();

const none = Symbol("none");

const numbers = [0, 1, 2, -1, 0.5, 10, 1000, 0.1, 1e21, 2 ** 53, 5e-324];

/** An instant around the scenarios' dates, written in UTC or with an offset, with or without fractional seconds. */
const instant = fc
  .tuple(
    fc.integer({ min: Date.UTC(2026, 9, 24), max: Date.UTC(2026, 9, 28) }),
    fc.constantFrom(0, 9 * 60, -(5 * 60 + 30)),
    fc.boolean(),
  )
  .map(([ms, offset, fraction]) => {
    const local = new Date(ms + offset * 60_000).toISOString().slice(0, fraction ? 23 : 19);
    const zone = Math.abs(offset);
    const hhmm = `${String(Math.floor(zone / 60)).padStart(2, "0")}:${String(zone % 60).padStart(2, "0")}`;
    return `${local}${offset === 0 ? "Z" : `${offset < 0 ? "-" : "+"}${hhmm}`}`;
  });

/**
 * Returns an arbitrary of the values of `schema` beyond explore's two representatives, or of `none` for a schema kind
 * that explore's representatives do not handle either. Strings come mostly from the scenarios' words, so that they can
 * reach the values that guards compare.
 */
function arbitraryOf(schema: z.ZodType, words: readonly string[]): fc.Arbitrary<unknown> {
  if (schema === datetime) return instant;
  if (schema === date) return fc.constantFrom("2026-10-24", "2026-10-25", "2026-10-26", "2026-10-27");
  if (schema instanceof z.ZodNullable)
    return fc.option(arbitraryOf(schema.unwrap() as z.ZodType, words), { nil: null });
  if (schema instanceof z.ZodOptional || schema instanceof z.ZodDefault)
    return arbitraryOf(schema.def.innerType as z.ZodType, words);
  if (schema instanceof z.ZodBoolean) return fc.boolean();
  if (schema instanceof z.ZodEnum) return fc.constantFrom(...(schema.options as readonly unknown[]));
  if (schema instanceof z.ZodLiteral) return fc.constantFrom(...schema.values);
  if (schema instanceof z.ZodUnion)
    return fc.oneof(...(schema.options as readonly z.ZodType[]).map((o) => arbitraryOf(o, words)));
  if (schema instanceof z.ZodArray) return fc.array(arbitraryOf(schema.element as z.ZodType, words), { maxLength: 3 });
  if (schema instanceof z.ZodString)
    return fc.oneof(
      { weight: 4, arbitrary: fc.constantFrom(...words, "a", "b", "c") },
      { weight: 1, arbitrary: fc.string({ maxLength: 4 }) },
      { weight: 1, arbitrary: fc.string({ unit: "binary", maxLength: 3 }) },
    );
  if (schema instanceof z.ZodNumber)
    return fc.oneof(
      fc.constantFrom(...numbers),
      fc.integer({ min: -3, max: 20 }),
      fc.double({ min: -10, max: 10, noNaN: true }).map((n) => n || 0),
      fc.double({ noNaN: true, noDefaultInfinity: true }).map((n) => n || 0),
    );
  if (schema instanceof z.ZodRecord)
    return fc.dictionary(
      arbitraryOf(schema.keyType as z.ZodType, words).filter((k): k is string => typeof k === "string"),
      arbitraryOf(schema.valueType as z.ZodType, words),
      { maxKeys: 2 },
    );
  if (schema instanceof z.ZodObject) return shapeArbitrary(schema.shape as Shape, words);
  return fc.constant(none);
}

/** An object of `shape`, without each optional or defaulted field half of the time. */
function shapeArbitrary(shape: Shape, words: readonly string[]): fc.Arbitrary<unknown> {
  const fields = Object.entries(shape);
  const model = Object.fromEntries(fields.map(([k, s]) => [k, arbitraryOf(s, words)]));
  const requiredKeys = fields.flatMap(([k, s]) => (s instanceof z.ZodOptional || s instanceof z.ZodDefault ? [] : [k]));
  return fc.record(model, { requiredKeys }).map((v) => (Object.values(v).includes(none) ? none : (v as unknown)));
}

/**
 * What kind of move comes next: one that explore enables, a move of the clock, or a line no one could write, which
 * mostly ends the execution and so comes rarely.
 */
const moveKind = () =>
  fc.oneof(
    { weight: 8, arbitrary: fc.constant("enabled" as const) },
    { weight: 1, arbitrary: fc.constant("clock" as const) },
    { weight: 1, arbitrary: fc.constant("invalid" as const) },
  );

/** A move forward of the clock, within a minute or within three days. */
const clockStep = () => fc.oneof(fc.integer({ min: 0, max: 60_000 }), fc.integer({ min: 0, max: 3 * 86_400_000 }));

const definitionOf = (spec: Spec, ref: { readonly service: string; readonly name: string }) =>
  spec.definitions.find((d) => d.service === ref.service && d.name === ref.name)?.definition;

/** The shape of the value a line writes, which a move may draw anew, and where the line keeps that value. */
function drawnValue(spec: Spec, line: Line): { shape: Shape; with: (value: unknown) => Line } | undefined {
  const literal = (value: unknown): Template => ({ value, holes: [] });
  switch (line.type) {
    case "request": {
      const d = definitionOf(spec, line.target) as AnyCommand | AnyQuery | undefined;
      return d === undefined ? undefined : { shape: d.input, with: (v) => ({ ...line, input: literal(v) }) };
    }
    case "emit": {
      const d = definitionOf(spec, line.event) as AnyEvent | undefined;
      return d === undefined ? undefined : { shape: d.payload, with: (v) => ({ ...line, payload: literal(v) }) };
    }
    case "operate": {
      if (line.screen.type !== "screen") return undefined;
      const screen = definitionOf(spec, line.screen.screen);
      const shape = (screen === undefined ? undefined : chartOf(screen)?.controls?.[line.control]?.payload) as
        | Shape
        | undefined;
      return { shape: shape ?? {}, with: (v) => ({ ...line, payload: literal(v) }) };
    }
    case "answer": {
      const answer = line.answer.value as Answer;
      if (line.request.type !== "request" || !("output" in answer)) return undefined;
      const d = definitionOf(spec, line.request.target) as AnyCommand | AnyQuery | undefined;
      const shape = d?.output as Shape | undefined;
      return shape === undefined
        ? undefined
        : { shape, with: (v) => ({ ...line, answer: literal({ ...answer, output: v }) }) };
    }
    default:
      return undefined;
  }
}

interface Found {
  readonly c: Case;
  readonly appended: readonly Line[];
  readonly difference?: Difference;
  readonly error?: unknown;
}

const lean = new Lean();
let found: Found | undefined;
let executions = 0;

/**
 * Draws a scenario and up to `depth` moves after it, each one that explore enables after the moves before it (with its
 * value drawn anew half of the time), a move of the clock, or a line no one could write. Executes every prefix in TS
 * with and without the evaluation cache and in Lean.
 */
const property = fc.property(fc.gen(), (g) => {
  const c = cases[g(fc.nat, cases.length - 1)] as Case;
  const { spec, sc } = c;
  let appended: Line[] = [];
  const each = (): Executed => {
    executions += 1;
    const { executed, difference } = executeEach(lean, spec, sc, appended);
    if (difference === undefined) return executed;
    found = { c, appended, difference };
    throw new Error(`the execution differs from ${difference.against}`);
  };
  try {
    let executed = each();
    const length = g(fc.integer, { min: 1, max: depth });
    for (let i = 0; i < length && !stopped(executed); i += 1) {
      let moves: Move[];
      try {
        moves = c.enabledAfter([...sc.lines, ...appended], executed);
      } catch (error) {
        if (error instanceof Halt) break;
        throw error;
      }
      const kind = g(moveKind);
      let move: Move;
      if (kind === "clock" || moves.length === 0) {
        const time = executed.world.now.add({ milliseconds: g(clockStep) }).toString();
        move = [{ type: "at", time }];
      } else if (kind === "invalid") {
        const invalid = invalidLines(spec, sc, executed, moves.flat());
        move = invalid[g(fc.nat, invalid.length - 1)] as Move;
      } else {
        move = moves[g(fc.nat, moves.length - 1)] as Move;
        const at = move.findIndex((l) => drawnValue(spec, l) !== undefined);
        const value = at === -1 ? undefined : drawnValue(spec, move[at] as Line);
        if (value !== undefined && g(fc.boolean)) {
          const drawn = g(shapeArbitrary, value.shape, c.words);
          if (drawn !== none) move = move.with(at, value.with(drawn));
        }
      }
      appended = [...appended, ...move];
      executed = each();
    }
  } catch (error) {
    if (found?.appended !== appended) found = { c, appended, error };
    throw error;
  }
});

/** The text around the first character where `a` and `b` differ. */
function firstDifference(a: string, b: string): string {
  let i = 0;
  while (i < a.length && a[i] === b[i]) i += 1;
  const from = Math.max(0, i - 200);
  return `cached TS: ...${a.slice(from, i + 200)}...\nother:     ...${b.slice(from, i + 200)}...`;
}

const started = performance.now();
console.log(`fuzz: seed ${seed}, ${runs} runs, up to ${depth} moves, ${cases.length} scenarios`);
const result = fc.check(property, { seed, numRuns: runs });
lean.close();
const seconds = ((performance.now() - started) / 1000).toFixed(0);

if (!result.failed) {
  console.log(`fuzz: no difference in ${executions} executions (${seconds}s)`);
  process.exit(0);
}
console.error(
  `fuzz: a difference after ${result.numRuns} runs (${seconds}s), seed ${seed}, path ${result.counterexamplePath}`,
);
console.error(`reproduce: npm run fuzz -- --seed ${seed} --runs ${runs} --depth ${depth}`);
if (found === undefined) throw result.errorInstance;
const { c, appended, difference, error } = found;
mkdirSync(fuzzFoundRoot, { recursive: true });
const file = join(fuzzFoundRoot, `${seed}.json`);
const fixture = { spec: c.root, scenario: { ...c.sc, lines: [...c.sc.lines, ...appended] } };
writeFileSync(file, `${JSON.stringify(fixture, null, 2)}\n`);
console.error(`spec ${c.root}, ${appended.length} lines appended: ${JSON.stringify(appended)}`);
console.error(difference === undefined ? String(error) : firstDifference(difference.ts, difference.other));
console.error(`wrote ${relative(tazuna, file)}; npm run lean:check runs it in test/run.diff.ts`);
process.exit(1);
