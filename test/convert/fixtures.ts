import fc from "fast-check";
import { z } from "zod";
import { type Defined, definedKey } from "../../src/convert/expression.ts";
import type { Expr } from "../../src/convert/ir.generated.ts";
import { bag } from "../../src/data/collections.ts";
import { date, datetime } from "../../src/data/datetime.ts";
import type { DefinitionRef } from "../../src/data/definitionRef.ts";
import type { Json, Shape } from "../../src/data/values.ts";
import { entity, type Records, type Ref, type Row, ref, refTarget, singleEntity } from "../../src/dsl/entity.ts";
import { emit } from "../../src/dsl/event.ts";
import { service } from "../../src/dsl/service.ts";
import type { Stored } from "../lean/protocol.generated.ts";

/**
 * A function whose IR has `op`, inputs of `shape` as JSON holds them, the records it reads of `entities`, and the
 * events that it emits, as its command lists them.
 */
export interface Fixture {
  readonly op: Expr["op"];
  readonly shape: Shape;
  readonly input: fc.Arbitrary<{ readonly [field: string]: Json }>;
  readonly records: fc.Arbitrary<readonly Stored[]>;
  readonly f: (args: never) => unknown;
  readonly events?: readonly DefinitionRef[];
}

const fixture = <S extends Shape>(
  op: Expr["op"],
  shape: S,
  input: fc.Arbitrary<{ readonly [field: string]: Json }>,
  f: (args: { readonly input: Row<S> }) => unknown,
): Fixture => ({ op, shape, input, records: fc.constant([]), f });

// Few distinct values, so that equal ones and empty ones come up often.
const text = fc.string({ maxLength: 3, unit: fc.constantFrom("a", "b", "é") });
const number = fc.oneof(fc.integer({ min: -2, max: 2 }), fc.double({ min: -3, max: 3, noNaN: true }));
const instant = fc
  .integer({ min: 0, max: 3 })
  .map((n) => Temporal.Instant.fromEpochMilliseconds(Date.UTC(2026, 0, 1) + n * 999).toString());
const day = fc.integer({ min: 0, max: 3 }).map((n) => new Date(Date.UTC(2026, 0, 30 + n)).toISOString().slice(0, 10));
const numbers = fc.array(number, { maxLength: 4 });

const item = { name: z.string() };
const itemOf = fc.record({ name: text });

const Task = entity({
  description: "A task",
  fields: { id: z.string(), title: z.string(), done: z.boolean(), at: datetime.nullable() },
  key: "id",
});
const Settings = singleEntity({ description: "The settings", fields: { limit: z.number().default(0) } });
export const entities = { Task, Settings };

/** What a loaded spec of the fixtures would define: the entity Task. */
export const defined: Defined = {
  constants: new Map(),
  entities: new Map([[definedKey(import.meta.filename, "Task"), "Task"]]),
};

/** The entity that createKey makes a key of for `r`, which throws, as TS's createKey does, unless it is ref(Task). */
export function keyOf(r: unknown): string {
  if (refTarget(r as Ref<typeof Task>) !== Task) throw new TypeError("createKey takes ref() of an entity of the spec");
  return "Task";
}

type CreateKey = (r: Ref<typeof Task>) => string;
const TaskId = ref(Task);
const ids = { task: TaskId };

const storedOf = fc
  .tuple(
    fc.uniqueArray(
      fc.record({ id: fc.constantFrom("a", "b", "c"), title: text, done: fc.boolean(), at: fc.option(instant) }),
      {
        selector: (t) => t.id,
        maxLength: 3,
      },
    ),
    fc.record({ limit: number }),
  )
  .map(([tasks, settings]): readonly Stored[] => [
    ...tasks.map((value) => ({ entity: "Task", key: value.id, value })),
    { entity: "Settings", value: settings },
  ]);

const recordFixture = <S extends Shape>(
  op: Expr["op"],
  shape: S,
  input: fc.Arbitrary<{ readonly [field: string]: Json }>,
  f: (args: {
    readonly input: Row<S>;
    readonly records: Records<typeof entities>;
    readonly createKey: CreateKey;
  }) => unknown,
): Fixture => ({ op, shape, input, records: storedOf, f });

const keyed = fc.record({ id: fc.constantFrom("a", "b", "d"), title: text });

const { command, condition, event } = service({ name: "fixtures", description: "The fixtures' events", entities });
const noted = event({ payload: { title: z.string() } });
const counted = event({ payload: { n: z.number() } });
const noting = command({ input: { title: z.string(), bag: bag(z.number()) }, emits: [noted, counted] }).decide(
  ({ input }) => [
    input.title === "" ? emit(counted, { n: 0 }) : emit(noted, { title: input.title }),
    input.bag.map((n) => emit(counted, { n })),
  ],
);

// Helpers that a fixture calls, which the converter inlines.
const between = (n: number, low: number, high: number) => low <= n && n <= high;
const tasksDone = condition(({ records }) => records.Task.every((t) => t.done));
function named(item: { readonly name: string } | null, name: string) {
  return item?.name === name;
}
const limit = 1;

export const fixtures: readonly Fixture[] = [
  fixture("undef", { note: z.string().optional() }, fc.record({ note: text }, { requiredKeys: [] }), ({ input }) =>
    input.note === undefined ? "none" : input.note,
  ),
  fixture("lit", { title: z.string() }, fc.record({ title: text }), ({ input }) => input.title === "a"),
  fixture("arg", { title: z.string() }, fc.record({ title: text }), ({ input }) => input.title),
  fixture("var", { ns: z.array(z.number()) }, fc.record({ ns: numbers }), ({ input }) => input.ns.some((n) => n > 0)),
  fixture("let", { a: z.string(), b: z.string() }, fc.record({ a: text, b: text }), ({ input }) => {
    const { a } = input;
    if (a === "") return input.b;
    return a;
  }),
  fixture(
    "ite",
    { n: z.number(), a: z.string(), b: z.string() },
    fc.record({ n: number, a: text, b: text }),
    ({ input }) => (input.n > 0 ? input.a : input.b),
  ),
  fixture(
    "and",
    { a: z.string(), n: z.number() },
    fc.record({ a: text, n: number }),
    ({ input }) => input.a && input.n,
  ),
  fixture("or", { a: z.string(), n: z.number() }, fc.record({ a: text, n: number }), ({ input }) => input.a || input.n),
  fixture(
    "coalesce",
    { note: z.string().nullable().optional(), title: z.string() },
    fc.record({ note: fc.option(text), title: text }, { requiredKeys: ["title"] }),
    ({ input }) => input.note ?? input.title,
  ),
  fixture("not", { n: z.number() }, fc.record({ n: number }), ({ input }) => !input.n),
  recordFixture("not", {}, fc.record({}), (args) => !tasksDone(args as never)),
  fixture("let", { ns: z.array(z.number()), n: z.number() }, fc.record({ ns: numbers, n: number }), ({ input }) =>
    input.ns.some((n) => between(input.n, n, limit)),
  ),
  fixture(
    "let",
    { items: z.array(z.object(item).nullable()), name: z.string() },
    fc.record({ items: fc.array(fc.option(itemOf), { maxLength: 3 }), name: text }),
    (args) => args.input.items.filter((i) => named(i, args.input.name)).length,
  ),
  fixture(
    "or",
    { a: z.string().nullable().optional(), n: z.number().nullable() },
    fc.record({ a: fc.option(text), n: fc.option(number) }, { requiredKeys: ["n"] }),
    ({ input }) => (input.a == null ? input.n != null : input.a),
  ),
  fixture(
    "eq",
    { a: z.string(), n: z.number().nullable() },
    fc.record({ a: text, n: fc.option(number) }),
    ({ input }) => input.a === "b" || input.n === null || input.n === 1,
  ),
  fixture("compare", { n: z.number(), m: z.number() }, fc.record({ n: number, m: number }), ({ input }) =>
    input.n <= input.m ? input.n < 0 : input.m >= 1,
  ),
  fixture(
    "compare",
    { at: datetime, until: datetime.nullable() },
    fc.record({ at: instant, until: fc.option(instant) }),
    ({ input }) =>
      input.until !== null && (Temporal.Instant.compare(input.at, input.until) > 0 || input.at.equals(input.until)),
  ),
  fixture("compare", { from: date, to: date }, fc.record({ from: day, to: day }), ({ input }) =>
    Temporal.PlainDate.compare(input.from, input.to) !== 0
      ? 0 >= Temporal.PlainDate.compare(input.from, input.to)
      : input.to.equals(input.from),
  ),
  fixture(
    "field",
    { item: z.object(item).nullable() },
    fc.record({ item: fc.option(itemOf) }),
    ({ input }) => input.item!.name === "a",
  ),
  fixture(
    "fieldOpt",
    { item: z.object(item).nullable().optional() },
    fc.record({ item: fc.option(itemOf) }, { requiredKeys: [] }),
    ({ input }) => input.item?.name,
  ),
  fixture("strLen", { title: z.string() }, fc.record({ title: text }), ({ input }) => input.title.length <= 1),
  fixture("startsWith", { a: z.string(), b: z.string() }, fc.record({ a: text, b: text }), ({ input }) =>
    input.a.startsWith(input.b),
  ),
  fixture("endsWith", { a: z.string(), b: z.string() }, fc.record({ a: text, b: text }), ({ input }) =>
    input.a.endsWith(input.b),
  ),
  fixture("strIncludes", { a: z.string(), b: z.string() }, fc.record({ a: text, b: text }), ({ input }) =>
    input.a.includes(input.b),
  ),
  fixture(
    "size",
    { ns: z.array(z.number()), bag: bag(z.number()) },
    fc.record({ ns: numbers, bag: numbers }),
    ({ input }) => input.ns.length === input.bag.size,
  ),
  fixture(
    "filter",
    { ns: z.array(z.number()) },
    fc.record({ ns: numbers }),
    ({ input }) => input.ns.filter((n) => n > 0).length,
  ),
  fixture(
    "filter",
    { bag: bag(z.number()) },
    fc.record({ bag: numbers }),
    ({ input }) => input.bag.filter((n) => n > 0).filter((n) => n < 2).size,
  ),
  fixture(
    "some",
    { items: z.array(z.object(item).nullable()) },
    fc.record({ items: fc.array(fc.option(itemOf), { maxLength: 3 }) }),
    ({ input }) => input.items.some((i) => i!.name === "a"),
  ),
  fixture(
    "some",
    { items: bag(z.object(item).nullable()) },
    fc.record({ items: fc.array(fc.option(itemOf), { maxLength: 3 }) }),
    ({ input }) => input.items.some((i) => i!.name === "a"),
  ),
  fixture(
    "every",
    { items: z.array(z.object(item)) },
    fc.record({ items: fc.array(itemOf, { maxLength: 3 }) }),
    ({ input }) => input.items.every(({ name }) => name !== "a"),
  ),
  fixture("every", { bag: bag(z.number()) }, fc.record({ bag: numbers }), ({ input }) =>
    input.bag.every((n) => n > -1),
  ),
  recordFixture(
    "table",
    { title: z.string() },
    fc.record({ title: text }),
    ({ input, records }) =>
      records.Task.filter((t) => t.done).size > 0 || records.Task.some((t) => t.title === input.title),
  ),
  recordFixture("table", {}, fc.record({}), ({ records }) =>
    records.Task.every((t) => t.at === null || Temporal.Instant.compare(t.at, t.at) === 0),
  ),
  recordFixture("single", { n: z.number() }, fc.record({ n: number }), ({ input, records }) =>
    records.Settings.limit > input.n ? records.Settings.limit : input.n,
  ),
  recordFixture(
    "lookup",
    { id: z.string(), title: z.string() },
    keyed,
    ({ input, records }) => records.Task.get(input.id)?.done === true || records.Task.get(input.id)?.title,
  ),
  recordFixture(
    "lookup",
    { id: z.string() },
    keyed,
    ({ input, records }) => records.Task.get(input.id) === undefined || records.Task.get(input.id)!.title === "a",
  ),
  fixture(
    "obj",
    { title: z.string(), note: z.string().optional() },
    fc.record({ title: text, note: text }, { requiredKeys: ["title"] }),
    ({ input }) => ({ a: input.title, b: input.note, c: { d: input.title === "a" } }),
  ),
  fixture(
    "arr",
    { title: z.string(), note: z.string().optional() },
    fc.record({ title: text, note: text }, { requiredKeys: ["title"] }),
    ({ input }) => [input.title, input.note],
  ),
  fixture("map", { ns: z.array(z.number()) }, fc.record({ ns: numbers }), ({ input }) => input.ns.map((n) => n > 0)),
  fixture("map", { bag: bag(z.number()).optional() }, fc.record({ bag: numbers }, { requiredKeys: [] }), ({ input }) =>
    (input.bag ?? []).filter((n) => n > 0).map((n) => n < 2),
  ),
  recordFixture("map", {}, fc.record({}), ({ records }) => records.Task.map((t) => ({ id: t.id, done: t.done }))),
  recordFixture("sum", {}, fc.record({}), ({ records }) => records.Task.sum((t) => (t.done ? 1 : 0))),
  fixture("sum", { bag: bag(z.number()) }, fc.record({ bag: numbers }), ({ input }) => input.bag.sum((n) => n)),
  fixture("min", { bag: bag(z.number()) }, fc.record({ bag: numbers }), ({ input }) => input.bag.min((n) => n)),
  recordFixture("max", {}, fc.record({}), ({ records }) =>
    records.Task.filter((t) => t.at !== null).max((t) => t.at as Temporal.Instant),
  ),
  recordFixture(
    "only",
    { title: z.string() },
    fc.record({ title: text }),
    ({ input, records }) => records.Task.filter((t) => t.title === input.title).only()?.id,
  ),
  fixture("sortedBy", { bag: bag(z.number()) }, fc.record({ bag: numbers }), ({ input }) =>
    input.bag.sortedBy((n) => n),
  ),
  recordFixture("sortedBy", {}, fc.record({}), ({ records }) =>
    records.Task.map((t) => ({ title: t.title, done: t.done ? 1 : 0 })).sortedBy((x) => x.done),
  ),
  fixture("concat", { ns: z.array(z.number()), n: z.number() }, fc.record({ ns: numbers, n: number }), ({ input }) => [
    input.n,
    ...input.ns,
    ...[input.n > 0],
    ...input.ns,
  ]),
  fixture("includes", { ns: z.array(z.number()), n: z.number() }, fc.record({ ns: numbers, n: number }), ({ input }) =>
    input.ns.includes(input.n),
  ),
  fixture(
    "format",
    { title: z.string(), n: z.number(), at: datetime, note: z.string().nullable().optional() },
    fc.record(
      {
        title: text,
        n: fc.oneof(number, fc.double({ noNaN: true, noDefaultInfinity: true })),
        at: instant,
        note: fc.option(text),
      },
      { requiredKeys: ["title", "n", "at"] },
    ),
    ({ input }) => `${input.title}: ${input.n} at ${input.at} ${input.note} ${input.n > 0}` + input.title,
  ),
  fixture("lit", { at: datetime, on: date }, fc.record({ at: instant, on: day }), ({ input }) =>
    Temporal.Instant.compare(input.at, Temporal.Instant.from("2026-01-01T09:00:01+09:00")) > 0
      ? input.on.toString()
      : Temporal.PlainDate.from("2026-01-31"),
  ),
  fixture(
    "arith",
    { n: z.int(), items: bag(z.object({ k: z.int().default(0) })), d: z.number() },
    fc.record({
      n: fc.integer({ min: -9, max: 9 }),
      items: fc.array(fc.record({ k: fc.integer({ min: -3, max: 3 }) }), { maxLength: 3 }),
      d: number,
    }),
    ({ input }) => {
      const { n } = input;
      return input.items.some((i) => i.k * 2 - -n === 3 + input.items.size) ? -n : n + input.items.sum((i) => i.k) - 1;
    },
  ),
  fixture(
    "decimal",
    { d: z.number(), e: z.number(), n: z.int() },
    fc.record({ d: number, e: fc.oneof(number, fc.constant(0)), n: fc.integer({ min: -9, max: 9 }) }),
    ({ input }) => {
      const { d, e, n } = input;
      const ratio = d / e;
      return [d + 0.1, d - e * 3.7, n / 3, -d, ratio, ratio > 1, ratio === d, `${d * 1e21} ${ratio}`, { q: e / n }];
    },
  ),
  recordFixture(
    "arith",
    {},
    fc.record({}),
    ({ records }) => records.Task.filter((t) => t.title.length + 1 > 2).size * 3,
  ),
  fixture(
    "timeAdd",
    { at: datetime, n: z.int() },
    fc.record({ at: instant, n: fc.integer({ min: -100, max: 100 }) }),
    ({ input }) => [
      input.at.add({ hours: input.n }),
      input.at.subtract({ minutes: 2 }),
      input.at.add({ milliseconds: input.n * 7 }),
    ],
  ),
  recordFixture("createKey", { title: z.string() }, fc.record({ title: text }), ({ input, createKey }) => ({
    first: createKey(ref(Task)),
    second: input.title === "" ? createKey(ids.task) : null,
    third: createKey(TaskId),
  })),
  recordFixture("concat", { bag: bag(z.number()) }, fc.record({ bag: numbers }), ({ input, records }) =>
    input.bag.concat(records.Task.map((t) => t.title.length)),
  ),
  {
    op: "emit",
    shape: noting.input,
    input: fc.record({ title: text, bag: numbers }),
    records: fc.constant([]),
    f: noting.decide as (args: never) => unknown,
    events: [
      { service: "fixtures", name: "noted" },
      { service: "fixtures", name: "counted" },
    ],
  },
];

const looping = (n: number): boolean => n > 0 && looping(n);

/** Functions with a construct outside the IR, each of which stays TS. */
export const outside: readonly ((args: {
  readonly input: Row<{ n: z.ZodNumber; title: z.ZodString; ns: z.ZodArray<z.ZodNumber> }>;
  readonly createKey: CreateKey;
}) => unknown)[] = [
  ({ input }) => input.n % 2 === 1,
  ({ input }) => Temporal.Now.instant().add({ hours: input.n }),
  ({ input }) => input.n ** 2,
  ({ input }) => input.title.trim() === "",
  ({ input }) => input.title < "b",
  ({ input }) => [...input.title].length === 1,
  ({ input }) => input.title + Temporal.Now.instant(),
  async ({ input }) => input.n > 0,
  // biome-ignore lint/suspicious/noDoubleEquals: == on other than null coerces, which the IR does not.
  ({ input }) => input.n == 1,
  (args) => [args].length === 1,
  ({ input }) => looping(input.n),
  ({ input, createKey }) => input.ns.map(() => createKey(TaskId)),
  ({ createKey }) => [createKey].length,
  ({ createKey }) => createKey(Task.fields.id as never),
];
