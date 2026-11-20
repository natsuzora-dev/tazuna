import assert from "node:assert/strict";
import { test } from "node:test";
import { z } from "zod";
import { BagValue } from "../src/data/bag.ts";
import { bag, written } from "../src/data/collections.ts";
import { strict } from "../src/data/schemaNode.ts";
import { canonicalJson } from "../src/data/values.ts";

test("canonicalJson of a copy key sorts object keys in UTF-16 order", () => {
  assert.equal(
    canonicalJson({ task: "t-1", at: { "10": 1, "9": [true, null], é: "é" }, Z: 1.5 }),
    '{"Z":1.5,"at":{"10":1,"9":[true,null],"é":"é"},"task":"t-1"}',
  );
});

test("written encodes a codec's part that fails its check, inside a discriminated union by the option that its tag names", () => {
  const cents = z.codec(z.string(), z.number().min(10), { decode: Number, encode: String });
  const schema = z.object({
    alone: cents,
    tagged: z.discriminatedUnion("unit", [
      z.object({ unit: z.literal("cents"), amount: cents }),
      z.object({ unit: z.literal("count"), amount: z.number() }),
    ]),
  });
  assert.deepEqual(written(schema, { alone: 5, tagged: { unit: "cents", amount: 5 } }), {
    alone: "5",
    tagged: { unit: "cents", amount: "5" },
  });
});

test("written writes a bag that fails its check inside a plain union as its elements", () => {
  const schema = z.object({ x: z.union([bag(z.string().min(3)), z.null()]) });
  assert.deepEqual(written(schema, { x: new BagValue(() => ["bb", "a"]) }), { x: ["a", "bb"] });
});

test("strict rejects a field that no object names, at any depth, and picks the union option that names every field", () => {
  const schema = strict(
    z.object({
      items: z.array(z.object({ n: z.number() })),
      part: z.union([z.object({ name: z.string() }), z.object({ name: z.string(), size: z.number() })]),
      tags: z.record(z.string(), z.object({ on: z.boolean() })),
      extra: z.looseObject({}),
    }),
  );
  const valid = { items: [{ n: 1 }], part: { name: "a", size: 2 }, tags: { a: { on: true } }, extra: { any: 1 } };
  assert.deepEqual(schema.parse(valid), valid);
  assert.equal(schema.safeParse({ ...valid, items: [{ n: 1, note: "x" }] }).success, false);
  assert.equal(schema.safeParse({ ...valid, tags: { a: { on: true, note: "x" } } }).success, false);
});

test("strict takes the fields of both sides of an intersection and rejects a field that neither names", () => {
  const schema = strict(z.intersection(z.object({ a: z.number() }), z.object({ b: z.number() })));
  assert.deepEqual(schema.parse({ a: 1, b: 2 }), { a: 1, b: 2 });
  assert.equal(schema.safeParse({ a: 1, b: 2, c: 3 }).success, false);
});
