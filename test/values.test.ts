import assert from "node:assert/strict";
import { test } from "node:test";
import { z } from "zod";
import { written } from "../src/data/collections.ts";
import { canonicalJson } from "../src/data/values.ts";

test("canonicalJson of a copy key sorts object keys in UTF-16 order", () => {
  assert.equal(
    canonicalJson({ task: "t-1", at: { "10": 1, "9": [true, null], é: "é" }, Z: 1.5 }),
    '{"Z":1.5,"at":{"10":1,"9":[true,null],"é":"é"},"task":"t-1"}',
  );
});

test("written encodes a value that fails its codec's check alike inside and outside a union", () => {
  const cents = z.codec(z.string(), z.number().min(10), { decode: Number, encode: String });
  const schema = z.object({
    alone: cents,
    inUnion: z.union([cents, z.boolean()]),
    inTuple: z.tuple([z.union([cents, z.null()])]),
    valid: z.union([cents, z.number()]),
  });
  assert.deepEqual(written(schema, { alone: 5, inUnion: 5, inTuple: [5], valid: 5 }), {
    alone: "5",
    inUnion: "5",
    inTuple: ["5"],
    valid: 5,
  });
});
