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
  schemaProperties,
  type TransitionStructure,
} from "../src/spec/structure.ts";
import { kindOf, pathOf } from "../src/spec/tree.ts";
import { check as canonical } from "../src/validation/canonical.ts";
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

const bases = (
  await Promise.all(
    examples.map(async (root) => {
      const loaded = await loadSpec(root);
      return loaded.kind === "structured"
        ? [{ name: relative(import.meta.dirname, root), structure: loaded.spec.structure }]
        : [];
    }),
  )
).flat();

for (const { name, structure } of bases)
  test(`${name}: TS and Lean find the same Illegal and structure NonCanonical violations`, () => {
    assert.deepEqual(lean.check(structure), check(structure));
    assert.deepEqual(lean.checkCanonical(structure), canonical(structure));
  });

type Pick3 = readonly [number, number, number];

const bagOf = (items: object) => ({ type: "array", items, "x-tazuna-bag": true });
const rows = (key: object) => ({
  type: "object",
  properties: { k: key },
  required: ["k"],
  additionalProperties: false,
});
// Context schemas for Schemas.check: sort keys that the encoded value orders or not, and unions told apart or not.
const contexts = [
  { type: "object", properties: { s: { type: "array", items: rows({ type: "integer" }), "x-tazuna-sorted-by": "k" } } },
  { type: "object", properties: { s: { type: "array", items: rows({ type: "string" }), "x-tazuna-sorted-by": "k" } } },
  { type: "object", properties: { u: { anyOf: [bagOf({ type: "number" }), { type: "null" }] } } },
  { type: "object", properties: { u: { anyOf: [rows({ type: "string" }), rows({ type: "string", const: "x" })] } } },
  { type: "object", properties: { u: { anyOf: [bagOf({ type: "number" }), bagOf({ type: "string" })] } } },
  {
    type: "object",
    properties: { u: { oneOf: [rows({ const: "a" }), { ...rows({ const: "b" }), items: bagOf({}) }] } },
  },
  {
    type: "object",
    properties: {
      s: { type: "array", items: rows({ type: "integer", "x-tazuna-codec": true }), "x-tazuna-sorted-by": "k" },
    },
  },
  {
    type: "object",
    properties: { u: { oneOf: [rows({ enum: ["a", "b"] }), { ...rows({ const: "c" }), items: bagOf({}) }] } },
  },
  {
    type: "object",
    properties: {
      u: {
        anyOf: [
          { ...rows({}), required: [] },
          { ...rows({}), properties: { n: bagOf({}) }, required: ["n"] },
        ],
      },
    },
  },
];

// Map key schemas for Schemas.check: no default, a default on a field, and a default below a field.
const mapKeys = [
  rows({ type: "string" }),
  rows({ type: "integer", default: 0 }),
  rows({ ...rows({ type: "string", default: "" }), default: {} }),
];

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
        ? ["plain", "history"]
        : ["plain", "final", "history"];
    if (state) (state as { kind: string }).kind = pick(kinds, b) ?? "plain";
  },
  screens(s, [a, b, c]) {
    const chart = pick(charts(s), a);
    const screen = pick(refsOf(s, ["screen"]), c);
    if (chart && screen) (chart.screens as Record<string, unknown>)[`k${b % 3}`] = screen;
  },
  input(s, [a]) {
    const chart = pick(charts(s), a);
    if (chart)
      (chart as { input: unknown }).input = {
        type: "object",
        properties: schemaProperties(chart.input).length > 0 ? {} : { x: { type: "string" } },
      };
  },
  context(s, [a, b]) {
    const chart = pick(charts(s), a);
    if (chart) (chart as { context: unknown }).context = pick(contexts, b);
  },
  mapKey(s, [a, b]) {
    const state = pick(
      charts(s).flatMap((c) => c.states.filter((st) => st.kind === "map")),
      a,
    );
    if (state?.kind === "map") (state.map as { key: unknown }).key = pick(mapKeys, b);
  },
  emits(s, [a, b, c]) {
    const command = pick(
      s.definitions.filter((d) => d.kind === "command"),
      a,
    );
    if (command?.kind !== "command") return;
    const event = pick(refsOf(s, ["event"]), c);
    if (event) (command as { emits: readonly unknown[] }).emits = [...command.emits.slice(0, b % 2), event];
  },
  automation(s, [a, b, c]) {
    const automation = pick(
      s.definitions.filter((d) => d.kind === "automation"),
      a,
    );
    if (automation?.kind !== "automation") return;
    const event = pick(refsOf(s, ["event"]), c);
    const command = pick(refsOf(s, ["command"]), c);
    if (b % 2 === 0 && event) (automation as { receives: unknown }).receives = event;
    else if (command) (automation as { command: unknown }).command = command;
  },
  members(s, [a, b, c]) {
    const contract = pick(s.contracts, a);
    if (contract)
      (contract.members as Record<string, unknown>)[`k${b % 3}`] =
        pick([null, ...refsOf(s, definitionKinds)], c) ?? null;
  },
  queries(s, [a, b, c]) {
    const chart = pick(charts(s), a);
    const query = pick(refsOf(s, ["query"]), c);
    if (chart && query) (chart.queries as Record<string, unknown>)[`k${b % 3}`] = query;
  },
  offers(s, [a, b]) {
    const chart = pick(
      charts(s).filter((c) => Object.keys(c.offers).length > 0),
      a,
    );
    const control = chart === undefined ? undefined : pick(Object.keys(chart.offers), b);
    if (chart && control !== undefined) delete (chart.offers as Record<string, unknown>)[control];
  },
  onRejected(s, [a, b]) {
    const written = [
      ...s.definitions.filter((d) => d.kind === "automation"),
      ...charts(s).flatMap((c) =>
        c.states.flatMap((st) => st.activities.filter((x) => x.keyword === "calls" || x.keyword === "sends")),
      ),
    ];
    const found = pick(written, a + b);
    if (found) (found as { onRejected: boolean }).onRejected = !found.onRejected;
  },
  external(s, [a]) {
    const service = pick(s.services, a);
    if (service) (service as { external: boolean }).external = !service.external;
  },
};

const runs = Number(process.env["TAZUNA_LEAN_CHECK_RUNS"] ?? 1000);
const mutable = bases.filter(({ structure }) => structure.definitions.some((d) => d.kind !== "entity"));

test("TS and Lean find the same Illegal and structure NonCanonical violations in mutated structures", (t) => {
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
        const tsCanonical = canonical(structure);
        for (const { kind } of [...ts, ...tsCanonical]) counts.set(kind, (counts.get(kind) ?? 0) + 1);
        const named = `${mutable[base]?.name} ${JSON.stringify(ops)}`;
        assert.deepEqual(lean.check(structure), ts, named);
        assert.deepEqual(lean.checkCanonical(structure), tsCanonical, named);
      },
    ),
    { numRuns: runs },
  );
  t.diagnostic(`findings ${JSON.stringify(Object.fromEntries(counts))}`);
});
