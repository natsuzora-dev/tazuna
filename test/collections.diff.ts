import assert from "node:assert/strict";
import { after, test } from "node:test";
import fc from "fast-check";
import { z } from "zod";
import { bag, fromJson, keyOrderIssue, set, sortCollections, sortedBy, toJson } from "../src/data/collections.ts";
import { date, datetime } from "../src/data/datetime.ts";
import { jsonSchema } from "../src/data/jsonSchema.ts";
import { canonicalJson, type Json, plain } from "../src/data/values.ts";
import { Lean } from "./lean/lean.ts";

const lean = new Lean();
after(() => lean.close());

/** A schema with the encoded values that it takes. `codec` says whether a codec is at any depth. */
interface Node {
  readonly schema: z.ZodType;
  readonly value: fc.Arbitrary<Json>;
  readonly codec: boolean;
}

const cents = z.codec(z.string(), z.int(), {
  decode: (text) => Math.round(Number(text) * 100),
  encode: (n) => (n / 100).toFixed(2),
});

const keys: readonly Node[] = [
  { schema: z.int(), value: fc.integer({ min: -2, max: 2 }), codec: false },
  {
    schema: datetime,
    value: fc.constantFrom("2026-10-25T09:00:00+09:00", "2026-10-25T00:00:00.5Z", "2026-10-24T23:00:00Z"),
    codec: true,
  },
  { schema: date, value: fc.constantFrom("2026-10-25", "2026-10-24", "2026-11-01"), codec: true },
];

const leaves: readonly Node[] = [
  ...keys,
  { schema: z.string(), value: fc.constantFrom("a", "B", "é", ""), codec: false },
  { schema: cents, value: fc.constantFrom("1.50", "0.20", "10.00"), codec: true },
];

const object = (fields: Readonly<Record<string, Node>>, optional: readonly string[] = []): Node => ({
  schema: z.object(
    Object.fromEntries(
      Object.entries(fields).map(([k, n]) => [k, optional.includes(k) ? n.schema.optional() : n.schema]),
    ),
  ),
  value: fc.record(Object.fromEntries(Object.entries(fields).map(([k, n]) => [k, n.value])), {
    requiredKeys: Object.keys(fields).filter((k) => !optional.includes(k)),
  }) as fc.Arbitrary<Json>,
  codec: Object.values(fields).some((n) => n.codec),
});

const composites = (node: fc.Arbitrary<Node>, free: fc.Arbitrary<Node>): fc.Arbitrary<Node>[] => [
  node.map((n) => ({ schema: bag(n.schema), value: fc.array(n.value, { maxLength: 4 }), codec: n.codec })),
  node.map((n) => ({
    schema: set(n.schema),
    value: fc.uniqueArray(n.value, { maxLength: 4, selector: canonicalJson }),
    codec: n.codec,
  })),
  node.map((n) => ({ schema: z.array(n.schema), value: fc.array(n.value, { maxLength: 3 }), codec: n.codec })),
  node.map((n) => ({ schema: n.schema.nullable(), value: fc.option(n.value, { nil: null }), codec: n.codec })),
  fc.tuple(fc.constantFrom(...keys), node).map(([k, n]) => {
    const row = object({ k, n });
    return {
      schema: sortedBy(row.schema as z.ZodObject<{ k: z.ZodInt; n: z.ZodType }>, "k"),
      value: fc.array(row.value, { maxLength: 4 }),
      codec: row.codec,
    };
  }),
  fc.tuple(node, node).map(([a, b]) => object({ a, b }, ["b"])),
  // Plain unions whose options only the closed fields or the required fields tell apart; a plain union holds no codec.
  fc.tuple(free, free).map(([a, b]) => {
    const [x, y] = [object({ x: a }, ["x"]), object({ y: b })];
    return { schema: z.union([x.schema, y.schema]), value: fc.oneof(x.value, y.value), codec: false };
  }),
  fc.tuple(free, free).map(([a, b]) => {
    const [x, y] = [object({ x: a }), object({ x: a, items: b })];
    return { schema: z.union([x.schema, y.schema]), value: fc.oneof(x.value, y.value), codec: false };
  }),
  fc.tuple(node, node).map(([a, b]) => {
    const tagged = (kind: z.ZodType, value: fc.Arbitrary<string>, n: Node) => ({
      schema: z.object({ kind, n: n.schema }),
      value: fc.record({ kind: value, n: n.value }) as fc.Arbitrary<Json>,
    });
    const [x, y] = [
      tagged(z.enum(["a", "b"]), fc.constantFrom("a", "b"), a),
      tagged(z.literal("c"), fc.constant("c"), b),
    ];
    return {
      schema: z.discriminatedUnion("kind", [x.schema, y.schema] as never),
      value: fc.oneof(x.value, y.value),
      codec: a.codec || b.codec,
    };
  }),
];

const { node } = fc.letrec<{ node: Node; free: Node }>((tie) => ({
  node: fc.oneof(
    { depthSize: "small", withCrossShrink: true },
    fc.constantFrom(...leaves),
    ...composites(tie("node"), tie("free")),
  ),
  free: tie("node").filter((n) => !n.codec),
}));

test("The TS engine's sortCollections sorts an encoded value as Lean's sortCollections does", () => {
  fc.assert(
    fc.property(
      node.chain((n) => n.value.map((json) => [n, json] as const)),
      ([n, json]) => {
        const encoded = plain(toJson(n.schema, fromJson(n.schema, json)));
        assert.deepEqual(sortCollections(jsonSchema(n.schema), encoded), lean.sort(jsonSchema(n.schema), encoded));
      },
    ),
    { numRuns: 400 },
  );
});

test("The TS engine's keyOrderIssue finds an encoded value out of key order where Lean's keyOrdered does", () => {
  fc.assert(
    fc.property(
      node.chain((n) => n.value.map((json) => [n, json] as const)),
      ([n, json]) => {
        const encoded = plain(toJson(n.schema, fromJson(n.schema, json)));
        const schema = jsonSchema(n.schema);
        assert.equal(keyOrderIssue(schema, encoded) === undefined, lean.keyOrdered(schema, encoded));
      },
    ),
    { numRuns: 400 },
  );
});
