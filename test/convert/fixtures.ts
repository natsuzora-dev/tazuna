import fc from "fast-check";
import { z } from "zod";
import type { Expr } from "../../src/convert/ir.generated.ts";
import { bag } from "../../src/data/collections.ts";
import { date, datetime } from "../../src/data/datetime.ts";
import type { Json, Shape } from "../../src/data/values.ts";
import type { Row } from "../../src/dsl/entity.ts";

/** A function whose IR has `op`, and inputs of `shape` as JSON holds them. */
export interface Fixture {
  readonly op: Expr["op"];
  readonly shape: Shape;
  readonly input: fc.Arbitrary<{ readonly [field: string]: Json }>;
  readonly f: (args: never) => unknown;
}

const fixture = <S extends Shape>(
  op: Expr["op"],
  shape: S,
  input: fc.Arbitrary<{ readonly [field: string]: Json }>,
  f: (args: { readonly input: Row<S> }) => unknown,
): Fixture => ({ op, shape, input, f });

// Few distinct values, so that equal ones and empty ones come up often.
const text = fc.string({ maxLength: 3, unit: fc.constantFrom("a", "b", "é") });
const number = fc.oneof(fc.integer({ min: -2, max: 2 }), fc.double({ min: -3, max: 3, noNaN: true }));
const instant = fc.integer({ min: 0, max: 3 }).map((n) => new Date(Date.UTC(2026, 0, 1) + n * 999).toISOString());
const day = fc.integer({ min: 0, max: 3 }).map((n) => new Date(Date.UTC(2026, 0, 30 + n)).toISOString().slice(0, 10));
const numbers = fc.array(number, { maxLength: 4 });

const item = { name: z.string() };
const itemOf = fc.record({ name: text });

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
];

/** Functions with a construct outside the IR, each of which stays TS. */
export const outside: readonly ((args: { readonly input: Row<{ n: z.ZodNumber; title: z.ZodString }> }) => unknown)[] =
  [
    ({ input }) => input.n + 1 > 2,
    ({ input }) => input.title.trim() === "",
    ({ input }) => input.title < "b",
    ({ input }) => `${input.title}!` === "a!",
    ({ input }) => [input.n].length === 1,
    (args) => args.input.n > 0,
    async ({ input }) => input.n > 0,
  ];
