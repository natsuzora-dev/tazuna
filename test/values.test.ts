import assert from "node:assert/strict";
import { test } from "node:test";
import { canonicalJson } from "../src/data/values.ts";

test("canonicalJson of a copy key sorts object keys in UTF-16 order", () => {
  assert.equal(
    canonicalJson({ task: "t-1", at: { "10": 1, "9": [true, null], é: "é" }, Z: 1.5 }),
    '{"Z":1.5,"at":{"10":1,"9":[true,null],"é":"é"},"task":"t-1"}',
  );
});
