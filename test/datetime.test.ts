import assert from "node:assert/strict";
import { test } from "node:test";
import { timeZone } from "../src/data/datetime.ts";

test("timeZone accepts the names that Temporal resolves as a named zone, in the spelling Temporal gives, and rejects offsets and other strings", () => {
  for (const name of ["UTC", "Etc/UTC", "GMT", "Europe/Kyiv", "Europe/Kiev", "Asia/Tokyo"])
    assert.equal(timeZone.safeParse(name).success, true, name);
  for (const name of ["asia/tokyo", "+09:00", "-05:00", "Z", "Nope/Zone", "", "2020-01-01T00:00Z[UTC]"])
    assert.equal(timeZone.safeParse(name).success, false, name);
});
