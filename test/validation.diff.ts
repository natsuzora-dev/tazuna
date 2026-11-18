import assert from "node:assert/strict";
import { relative } from "node:path";
import { after, test } from "node:test";
import fc from "fast-check";
import { loadSpec } from "../src/load/load.ts";
import type { Structure } from "../src/spec/structure.generated.ts";
import {
  type ChartStructure,
  type DefinitionStructure,
  definitionKinds,
  type TransitionStructure,
} from "../src/spec/structure.ts";
import { kindOf, pathOf } from "../src/spec/tree.ts";
import { check } from "../src/validation/check.ts";
import { groupExamples, runExamples } from "./examples.ts";
import { Lean } from "./lean/lean.ts";

const lean = new Lean();
after(() => lean.close());

// Every example: the Illegal examples alone hold few contracts and scenarios.
const examples = [
  ...groupExamples("load"),
  ...groupExamples("validation"),
  ...groupExamples("verify"),
  ...groupExamples("explore"),
  ...runExamples(),
];

const bases = await Promise.all(
  examples.map(async (root) => ({
    name: relative(import.meta.dirname, root),
    structure: (await loadSpec(root)).spec.structure,
  })),
);

for (const { name, structure } of bases)
  test(`${name}: TS and Lean find the same Illegal violations in the structure`, () => {
    assert.deepEqual(lean.check(structure), check(structure));
  });

type Pick3 = readonly [number, number, number];

const pick = <T>(items: readonly T[], k: number): T | undefined => items[k % Math.max(items.length, 1)];
const charts = (s: Structure) =>
  s.definitions.filter((d): d is ChartStructure => d.kind === "machine" || d.kind === "screen");
const refsOf = (s: Structure, kinds: readonly DefinitionStructure["kind"][]) =>
  s.definitions.filter((d) => kinds.includes(d.kind)).map((d) => ({ service: d.service, name: d.name }));
const transitionsOf = (c: ChartStructure) => [c.on, ...c.states.map((st) => st.transitions)];
const mapAbove = (c: ChartStructure, name: string | null) =>
  name === null
    ? undefined
    : pathOf(c, name)
        .slice(0, -1)
        .find((a) => kindOf(c, a) === "map");
/**
 * Returns the targets that the DSL allows from `source`: the states under its own map state, or outside every map
 * state.
 */
const targetsFrom = (c: ChartStructure, source: string | null) =>
  c.states.map((st) => st.name).filter((n) => mapAbove(c, n) === mapAbove(c, source));

const nextReenter = new Map<boolean | null, boolean | null>([
  [null, false],
  [false, true],
  [true, null],
]);

/** Mutations keep the tree shape (paths, parents, children) and change only values that check reads. */
const mutations: Record<string, (s: Structure, k: Pick3) => void> = {
  target(s, [a, b, c]) {
    const chart = pick(charts(s), a);
    const t = pick(transitionsOf(chart ?? ({ on: [], states: [] } as never)).flat(), b);
    if (chart && t) (t as { target: string | null }).target = pick([null, ...targetsFrom(chart, t.source)], c) ?? null;
  },
  guard(s, [a, b]) {
    const t = pick(
      charts(s).flatMap((c) => transitionsOf(c).flat()),
      a + b,
    );
    if (t) (t as { guards: readonly string[] }).guards = t.guards.length > 0 ? [] : ["g"];
  },
  reenter(s, [a]) {
    const t = pick(
      charts(s).flatMap((c) => transitionsOf(c).flat()),
      a,
    );
    if (t) (t as { reenter: boolean | null }).reenter = nextReenter.get(t.reenter) ?? null;
  },
  always(s, [a, b, c]) {
    const chart = pick(charts(s), a);
    const state = chart && pick(chart.states, b);
    if (!chart || !state) return;
    const t: TransitionStructure = {
      source: state.name,
      trigger: { type: "always" },
      index: state.transitions.length,
      target: pick([null, ...targetsFrom(chart, state.name)], c) ?? null,
      guards: c % 3 === 0 ? ["g"] : [],
      reenter: pick([null, false, true], c) ?? null,
    };
    (state.transitions as TransitionStructure[]).push(t);
  },
  kind(s, [a, b]) {
    const chart = pick(charts(s), a);
    const state =
      chart &&
      pick(
        chart.states.filter((st) => st.children.length === 0),
        a,
      );
    // The DSL puts no final state under a map state.
    const kinds =
      chart && state && mapAbove(chart, state.name) !== undefined
        ? ["atomic", "history"]
        : ["atomic", "final", "history"];
    if (state) (state as { kind: string }).kind = pick(kinds, b) ?? "atomic";
  },
  screens(s, [a, b, c]) {
    const chart = pick(charts(s), a);
    if (chart)
      (chart.screens as Record<string, unknown>)[`k${b % 3}`] = pick([null, ...refsOf(s, ["screen"])], c) ?? null;
  },
  input(s, [a]) {
    const chart = pick(charts(s), a);
    if (chart) (chart as { input: readonly string[] }).input = chart.input.length > 0 ? [] : ["x"];
  },
  emits(s, [a, b, c]) {
    const command = pick(
      s.definitions.filter((d) => d.kind === "command"),
      a,
    );
    if (command?.kind !== "command") return;
    const events = refsOf(s, ["event"]);
    (command as { emits: readonly unknown[] }).emits = [...command.emits.slice(0, b % 2), pick(events, c) ?? null];
  },
  automation(s, [a, b, c]) {
    const automation = pick(
      s.definitions.filter((d) => d.kind === "automation"),
      a,
    );
    if (automation?.kind !== "automation") return;
    if (b % 2 === 0) (automation as { receives: unknown }).receives = pick(refsOf(s, ["event"]), c) ?? null;
    else (automation as { command: unknown }).command = pick(refsOf(s, ["command"]), c) ?? null;
  },
  members(s, [a, b, c]) {
    const contract = pick(s.contracts, a);
    if (contract)
      (contract.members as Record<string, unknown>)[`k${b % 3}`] =
        pick([null, ...refsOf(s, definitionKinds)], c) ?? null;
  },
  queries(s, [a, b, c]) {
    const chart = pick(charts(s), a);
    if (chart)
      (chart.queries as Record<string, unknown>)[`k${b % 3}`] = pick([null, ...refsOf(s, ["query"])], c) ?? null;
  },
  offers(s, [a, b]) {
    const chart = pick(
      charts(s).filter((c) => Object.keys(c.offers).length > 0),
      a,
    );
    const control = chart === undefined ? undefined : pick(Object.keys(chart.offers), b);
    if (chart && control !== undefined) delete (chart.offers as Record<string, unknown>)[control];
  },
  external(s, [a]) {
    const service = pick(s.services, a);
    if (service) (service as { external: boolean }).external = !service.external;
  },
};

const runs = Number(process.env["TAZUNA_LEAN_CHECK_RUNS"] ?? 1000);
const mutable = bases.filter(({ structure }) => structure.definitions.some((d) => d.kind !== "entity"));

test("TS and Lean find the same Illegal violations in mutated structures", (t) => {
  const counts = new Map<string, number>();
  fc.assert(
    fc.property(
      fc.nat(mutable.length - 1),
      fc.array(fc.tuple(fc.constantFrom(...Object.keys(mutations)), fc.nat(), fc.nat(), fc.nat()), {
        minLength: 1,
        maxLength: 8,
      }),
      (base, ops) => {
        const structure = structuredClone((mutable[base] as (typeof mutable)[number]).structure);
        for (const [op, a, b, c] of ops) mutations[op]?.(structure, [a, b, c]);
        const ts = check(structure);
        for (const { kind } of ts) counts.set(kind, (counts.get(kind) ?? 0) + 1);
        assert.deepEqual(lean.check(structure), ts, `${mutable[base]?.name} ${JSON.stringify(ops)}`);
      },
    ),
    { numRuns: runs },
  );
  t.diagnostic(`findings ${JSON.stringify(Object.fromEntries(counts))}`);
});
