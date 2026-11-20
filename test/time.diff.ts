import assert from "node:assert/strict";
import { after, test } from "node:test";
import fc from "fast-check";
import { scenarioTime } from "../src/scenario/lower.ts";
import { Lean } from "./lean/lean.ts";

const lean = new Lean();
after(() => lean.close());

const digits = (n: number) => fc.stringMatching(new RegExp(`^\\d{${n}}$`));
const pick = <T>(...xs: T[]) => fc.constantFrom(...xs);

test("TS reads the time of a start or clock line as Lean's scenarioTime? does", () => {
  const time = fc
    .tuple(
      pick("2026", "0000", "9999", "1970", "2024"),
      pick("01", "02", "12", "13", "00"),
      pick("01", "28", "29", "30", "31", "32"),
      pick("00", "09", "23", "24"),
      pick("00", "59", "60"),
      pick("", ":00", ":59", ":60"),
      fc.oneof(pick("", ".", ".5", ".123", ".000000", ".0001", ".001000", ".123456789", ".1234567890"), digits(4)),
      pick("Z", "z", "+09:00", "-23:59", "+24:00", "+0900", "+09", ""),
    )
    .map(
      ([y, mo, d, h, mi, s, f, o]) =>
        `${y}-${mo}-${d}T${h}:${mi}${s}${f.startsWith(".") || f === "" ? f : `.${f}`}${o}`,
    );
  fc.assert(
    fc.property(time, (text) => {
      assert.equal(scenarioTime(text), lean.scenarioTime(text));
    }),
    { numRuns: 400 },
  );
});
