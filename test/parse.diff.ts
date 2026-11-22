import assert from "node:assert/strict";
import { after, test } from "node:test";
import fc from "fast-check";
import { z } from "zod";
import { bag, set, sortedBy, toJson } from "../src/data/collections.ts";
import { objectSchema } from "../src/data/jsonSchema.ts";
import { date, duration, instant } from "../src/data/time.ts";
import { type Json, plain, type Shape, strictObjectOf } from "../src/data/values.ts";
import { Lean } from "./lean/lean.ts";

const lean = new Lean();
after(() => lean.close());

/** What TS's parse gives for `value`: the value encoded again, Zod's issues, or a throw. */
function parsedByZod(shape: Shape, value: Json): { value?: Json; issues?: Json; thrown: boolean } {
  const object = strictObjectOf(shape);
  try {
    const parsed = object.safeParse(value);
    return parsed.success
      ? { value: plain(toJson(object, parsed.data)), thrown: false }
      : { issues: plain(parsed.error.issues), thrown: false };
  } catch {
    return { thrown: true };
  }
}

const text = fc.string({ maxLength: 4, unit: fc.constantFrom("a", "b", "x", "é", "😀") });
const scalar = fc.oneof(
  text,
  fc.integer({ min: -3, max: 3 }),
  fc.double({ noNaN: true, noDefaultInfinity: true, min: -1e3, max: 1e3 }),
  fc.constantFrom(2 ** 60, -(2 ** 60), 0.5, null, true, false),
);
const json: fc.Arbitrary<Json> = fc.letrec<{ value: Json }>((tie) => ({
  value: fc.oneof(
    { depthSize: "small" },
    scalar,
    fc.array(tie("value"), { maxLength: 3 }),
    fc.dictionary(fc.constantFrom("a", "k", "x", "1"), tie("value"), { maxKeys: 3 }),
  ),
})).value;
const instantValue = fc.oneof(
  fc.constantFrom(1_767_225_600_000, -1, 0.5, 2 ** 53, "2026-01-01T00:00:00Z"),
  fc.integer({ min: -3, max: 3 }),
);
const day = fc.constantFrom("2026-01-31", "2026-02-30", "2024-02-29", "0000-02-29", "26-01-01", 20260131);

/** A schema's fields and values of them: often of the field's own kind, sometimes anything. */
const fixtures: readonly { readonly shape: Shape; readonly fields: Readonly<Record<string, fc.Arbitrary<Json>>> }[] = [
  {
    shape: { s: z.string().min(1).max(3), n: z.number().positive(), i: z.int().min(-1), b: z.boolean() },
    fields: { s: text, n: scalar, i: scalar, b: scalar },
  },
  {
    shape: {
      p: z.string().startsWith("x").endsWith("a"),
      q: z.string().includes("b").length(2),
      m: z.number().multipleOf(0.1).lt(5),
      w: z.number().int().max(2),
    },
    fields: { p: text, q: text, m: scalar, w: scalar },
  },
  {
    shape: {
      o: z.string().optional(),
      d: z.string().default("d"),
      u: z.string().nullable(),
      v: z.int().nullable().optional(),
      e: z.enum(["a", "b"]).default("a"),
      l: z.literal(1),
      ls: z.literal(["a", 2]),
      k: z.unknown(),
    },
    fields: { o: text, d: text, u: scalar, v: scalar, e: text, l: scalar, ls: scalar, k: json },
  },
  {
    shape: {
      u: z.union([z.string().min(2), z.int()]),
      w: z.union([z.string(), z.boolean()]),
      n: z.union([z.object({ a: z.string() }), z.null()]),
      d: z.discriminatedUnion("k", [
        z.object({ k: z.literal("a") }),
        z.object({ k: z.literal("x"), x: z.int() }),
        z.object({ k: z.literal(1), a: z.string().optional() }),
      ]),
    },
    fields: { u: scalar, w: scalar, n: json, d: json },
  },
  {
    shape: {
      a: z.array(z.int()).min(1).max(2),
      b: bag(z.string().max(1)),
      s: set(z.object({ a: z.int() })).max(2),
      r: sortedBy(z.object({ at: z.int(), x: z.string().optional() }), "at"),
      o: z.object({ x: z.object({ y: z.string() }), z: z.array(z.string()).optional() }),
    },
    fields: {
      a: fc.array(scalar, { maxLength: 3 }),
      b: fc.array(text, { maxLength: 3 }),
      s: fc.array(fc.record({ a: fc.integer({ min: 0, max: 1 }) }), { maxLength: 3 }),
      r: fc.array(fc.record({ at: fc.integer({ min: 0, max: 2 }) }), { maxLength: 3 }),
      o: json,
    },
  },
  {
    shape: { at: instant, on: date, for: duration, maybe: instant.optional(), list: z.array(instant) },
    fields: {
      at: instantValue,
      on: day,
      for: instantValue,
      maybe: fc.oneof(instantValue, scalar),
      list: fc.array(instantValue, { maxLength: 2 }),
    },
  },
  {
    shape: {
      m: z.string().min(2, "too short"),
      s: z.string({ error: "no text" }).max(1),
      o: z.strictObject({ a: z.int() }, { error: "no object" }),
      u: z.union([z.string(), z.int()], { error: "no option" }),
      e: z.enum(["a", "b"], { error: "no letter" }),
      i: z.int({ error: "no integer" }).min(3, "below three"),
      a: z.string().min(2, { error: "short", abort: true }).max(1),
    },
    fields: { m: scalar, s: scalar, o: json, u: scalar, e: scalar, i: scalar, a: scalar },
  },
];

/** A value of a fixture's shape: some fields left out, some given anything, and at times a field it lacks. */
const valuesOf = (fields: Readonly<Record<string, fc.Arbitrary<Json>>>): fc.Arbitrary<Json> =>
  fc.oneof(
    { weight: 4, arbitrary: fc.record(fields, { requiredKeys: [] }) as fc.Arbitrary<Json> },
    {
      weight: 1,
      arbitrary: fc.record(Object.fromEntries([...Object.keys(fields), "extra"].map((k) => [k, json])), {
        requiredKeys: [],
      }) as fc.Arbitrary<Json>,
    },
    { weight: 1, arbitrary: json },
  );

for (const [i, { shape, fields }] of fixtures.entries())
  test(`fixture ${i}: Lean parses by its JSON Schema as Zod parses, issues and encoding included`, () => {
    const schema = objectSchema(shape) as Json;
    fc.assert(
      fc.property(valuesOf(fields), (value) => {
        const parsed = lean.parse(schema, value);
        assert.ok(parsed !== undefined, "Lean parses by the schema");
        const { value: v, issues, thrown } = parsed;
        assert.deepEqual(
          { ...(v === undefined || v === null ? {} : { value: v }), ...(issues ? { issues } : {}), thrown },
          parsedByZod(shape, value),
        );
      }),
      { numRuns: 300 },
    );
  });

test("Lean leaves to Zod the schemas that check reports as Restricted: a string format, a refinement, an overwrite, a message that is a function, a record, or a recursion", () => {
  type Tree = { readonly children: readonly Tree[] };
  const tree: z.ZodType<Tree> = z.lazy(() => z.object({ children: z.array(tree) }));
  for (const field of [
    z.email(),
    z.string().regex(/a/),
    z.string().refine((s) => s !== ""),
    z.string().trim(),
    z.string({ error: (issue) => String(issue.input) }),
    tree,
    z.record(z.string(), z.int()),
    z.iso.datetime(),
  ])
    assert.equal(lean.parse(objectSchema({ field }) as Json, {}), undefined, JSON.stringify(objectSchema({ field })));
});
