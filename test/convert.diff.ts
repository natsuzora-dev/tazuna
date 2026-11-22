import assert from "node:assert/strict";
import { after, test } from "node:test";
import fc from "fast-check";
import type { Expr } from "../src/convert/ir.generated.ts";
import { Converter } from "../src/convert/program.ts";
import { bagValues } from "../src/data/bag.ts";
import { decoded } from "../src/data/collections.ts";
import { type Json, objectOf } from "../src/data/values.ts";
import { fixtures, outside } from "./convert/fixtures.ts";
import { Lean } from "./lean/lean.ts";

const lean = new Lean();
const converter = new Converter();
after(() => {
  converter.close();
  lean.close();
});

/** Every operation of the IR. */
const ops = [
  "undef",
  "lit",
  "arg",
  "var",
  "let",
  "ite",
  "and",
  "or",
  "coalesce",
  "not",
  "eq",
  "compare",
  "field",
  "fieldOpt",
  "strLen",
  "startsWith",
  "endsWith",
  "strIncludes",
  "size",
  "filter",
  "some",
  "every",
] as const satisfies readonly Expr["op"][];
const listsEveryOp: [Exclude<Expr["op"], (typeof ops)[number]>] extends [never] ? true : false = true;

function opsOf(value: unknown, found = new Set<string>()): Set<string> {
  if (Array.isArray(value)) for (const v of value) opsOf(v, found);
  else if (value !== null && typeof value === "object") {
    const { op } = value as { readonly op?: unknown };
    if (typeof op === "string") found.add(op);
    for (const v of Object.values(value)) opsOf(v, found);
  }
  return found;
}

/** A value that a TS function returned, as JSON holds it: a Bag as its values, an instant or date as its text. */
function jsonOf(value: unknown): Json | undefined {
  const values = bagValues(value);
  if (values !== undefined) return values.map((v) => jsonOf(v) ?? null);
  if (value instanceof Temporal.Instant || value instanceof Temporal.PlainDate) return value.toString();
  if (Array.isArray(value)) return value.map((v) => jsonOf(v) ?? null);
  if (value !== null && typeof value === "object")
    return Object.fromEntries(Object.entries(value).map(([k, v]) => [k, jsonOf(v) ?? null]));
  return value as Json | undefined;
}

const converted = fixtures.map((fixture) => ({ fixture, ir: converter.convert(fixture.f, ["input"]) }));

for (const [i, { fixture, ir }] of converted.entries())
  test(`fixture ${i} (${fixture.op}) converts to IR with ${fixture.op}, which Lean evaluates as TS runs the function on random inputs`, () => {
    if ("unconverted" in ir) assert.fail(`not converted: ${ir.unconverted}`);
    assert.ok(opsOf(ir).has(fixture.op), JSON.stringify(ir));
    const schema = objectOf(fixture.shape);
    fc.assert(
      fc.property(fixture.input, (generated) => {
        const json = JSON.parse(JSON.stringify(generated)) as Json;
        let ts: { readonly value?: Json } | { readonly issue: "thrown" };
        try {
          const value = jsonOf(fixture.f({ input: decoded(schema, json) } as never));
          ts = value === undefined ? {} : { value };
        } catch {
          ts = { issue: "thrown" };
        }
        const { value, issue } = lean.evaluate(ir, json);
        assert.deepEqual(issue === undefined ? (value === undefined ? {} : { value }) : { issue: issue.kind }, ts);
      }),
    );
  });

test("every operation of the IR has a fixture", () => {
  assert.ok(listsEveryOp);
  const covered = new Set(fixtures.map((f) => f.op));
  assert.deepEqual(
    ops.filter((op) => !covered.has(op)),
    [],
  );
});

for (const [i, f] of outside.entries())
  test(`function ${i} with a construct outside the IR stays TS`, () => {
    const ir = converter.convert(f, ["input"]);
    assert.ok("unconverted" in ir, JSON.stringify(ir));
  });
