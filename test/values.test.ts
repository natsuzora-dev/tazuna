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
