import assert from "node:assert/strict";
import { test } from "node:test";
import fc from "fast-check";
import { addDays, type DateLabel, parseInstant } from "../src/data/time.ts";

test("parseInstant reads an ISO text with seconds and Z or an offset as Date.parse does, and rejects other texts", () => {
  const pad = (n: number, width = 2) => String(n).padStart(width, "0");
  const text = fc
    .tuple(
      fc.integer({ min: 0, max: 9999 }),
      fc.integer({ min: 1, max: 12 }),
      fc.integer({ min: 1, max: 28 }),
      fc.integer({ min: 0, max: 23 }),
      fc.integer({ min: 0, max: 59 }),
      fc.integer({ min: 0, max: 59 }),
      fc.constantFrom("", ".5", ".123"),
      fc.constantFrom("Z", "+09:00", "-23:59", "+00:00"),
    )
    .map(([y, mo, d, h, mi, s, f, o]) => `${pad(y, 4)}-${pad(mo)}-${pad(d)}T${pad(h)}:${pad(mi)}:${pad(s)}${f}${o}`);
  fc.assert(fc.property(text, (t) => assert.equal(parseInstant(t), Date.parse(t), t)));
  for (const t of [
    "2026-10-25T10:00+09:00",
    "2026-10-25T10:00:00",
    "2026-10-25T10:00:00+0900",
    "2026-02-30T10:00:00Z",
    "2026-10-25T24:00:00Z",
    "2026-10-25T10:00:00.1234Z",
    "2026-10-25",
  ])
    assert.throws(() => parseInstant(t), RangeError, t);
});

test("addDays moves a date label by whole days across months, years and leap days, within years 0000 through 9999", () => {
  const day = (t: string) => t as DateLabel;
  assert.equal(addDays(day("2024-02-28"), 1), "2024-02-29");
  assert.equal(addDays(day("2023-02-28"), 1), "2023-03-01");
  assert.equal(addDays(day("2026-12-31"), 1), "2027-01-01");
  assert.equal(addDays(day("2026-03-01"), -1), "2026-02-28");
  assert.equal(addDays(day("0000-03-01"), -1), "0000-02-29");
  assert.throws(() => addDays(day("9999-12-31"), 1), RangeError);
  assert.throws(() => addDays(day("0000-01-01"), -1), RangeError);
  assert.throws(() => addDays(day("2026-02-30"), 0), RangeError);
});
