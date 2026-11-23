import assert from "node:assert/strict";
import { test } from "node:test";
import { z } from "zod";
import { BagValue } from "../../src/data/bag.ts";
import { bag, encoded } from "../../src/data/collections.ts";
import { strict } from "../../src/data/schemaNode.ts";
import { canonicalJson } from "../../src/data/values.ts";

test("canonicalJson of a copy key sorts object keys in UTF-16 order", () => {
  assert.equal(
    canonicalJson({ task: "t-1", at: { "10": 1, "9": [true, null], é: "é" }, Z: 1.5 }),
    '{"Z":1.5,"at":{"10":1,"9":[true,null],"é":"é"},"task":"t-1"}',
  );
});

test("encoded reports a codec's part that fails its check, inside a discriminated union by the option that its tag names", () => {
  const cents = z.codec(z.string(), z.number().min(10), { decode: Number, encode: String });
  const schema = z.object({
    alone: cents,
    tagged: z.discriminatedUnion("unit", [
      z.object({ unit: z.literal("cents"), amount: cents }),
      z.object({ unit: z.literal("count"), amount: z.number() }),
    ]),
  });
  const json = encoded(schema, { alone: 5, tagged: { unit: "cents", amount: 5 } });
  assert.ok("error" in json);
  assert.deepEqual(
    json.error.issues.map((i) => i.path),
    [["alone"], ["tagged", "amount"]],
  );
  assert.deepEqual(encoded(schema, { alone: 15, tagged: { unit: "cents", amount: 15 } }), {
    encoded: { alone: "15", tagged: { unit: "cents", amount: "15" } },
  });
});

test("encoded writes a bag that fails its check inside a plain union as its elements, in the order it holds them", () => {
  const schema = z.object({ x: z.union([bag(z.string().min(3)), z.null()]) });
  assert.deepEqual(encoded(schema, { x: new BagValue(() => ["bb", "a"]) }), { encoded: { x: ["bb", "a"] } });
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
