import assert from "node:assert/strict";
import { after, test } from "node:test";
import fc from "fast-check";
import { z } from "zod";
import type { Keys, ReadPart, Stored } from "../src/cli/protocol.generated.ts";
import type { Typed } from "../src/convert/expression.ts";
import { Converter } from "../src/convert/program.ts";
import { bagValues, NotOnly } from "../src/data/bag.ts";
import { decoded } from "../src/data/collections.ts";
import { type Json, objectOf, type Shape } from "../src/data/values.ts";
import type { Expr } from "../src/spec/ir.generated.ts";
import { defined, entities, fixtures, keyOf, outside } from "./convert/fixtures.ts";
import { type RecordSource, recordsView } from "./convert/records.ts";
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
  "table",
  "single",
  "lookup",
  "obj",
  "arr",
  "map",
  "sum",
  "min",
  "max",
  "only",
  "sortedBy",
  "concat",
  "emit",
  "createKey",
  "includes",
  "format",
  "arith",
  "decimal",
  "addDays",
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

/** An emit, which Lean writes without its event: the shadow check of the diff tests compares the events. */
const isEmit = (value: unknown): value is { readonly payload: unknown } =>
  value !== null && typeof value === "object" && (value as { readonly kind?: unknown }).kind === "emit";

/**
 * A value that a TS function returned, as JSON.stringify writes it: a Bag as its values, and an undefined field left
 * out.
 */
function jsonOf(value: unknown): Json | undefined {
  const values = bagValues(value);
  if (values !== undefined) return values.map((v) => jsonOf(v) ?? null);
  if (isEmit(value)) return { kind: "emit", payload: jsonOf(value.payload) ?? null };
  if (Array.isArray(value)) return value.map((v) => jsonOf(v) ?? null);
  if (value !== null && typeof value === "object")
    return Object.fromEntries(
      Object.entries(value).flatMap(([k, v]) => {
        const json = jsonOf(v);
        return json === undefined ? [] : [[k, json]];
      }),
    );
  return value as Json | undefined;
}

/** `stored` as TS's records view reads them, with each part it reads noted once in `reads`, as Lean's read log does. */
function sourceOf(stored: readonly Stored[], reads: ReadPart[]): RecordSource {
  const note = (part: ReadPart) => {
    if (!reads.some((r) => r.entity === part.entity && r.key === part.key && r.field === part.field)) reads.push(part);
  };
  const keyed = (entity: string) => stored.filter((s) => s.entity === entity && s.key !== undefined);
  return {
    keys: (entity) => {
      note({ entity });
      return keyed(entity).map((s) => s.key as string);
    },
    exists: (entity, key) => {
      note({ entity, key });
      return keyed(entity).some((s) => s.key === key);
    },
    field: (entity, key, field) => {
      note(key === undefined ? { entity, field } : { entity, key, field });
      const row = stored.find((s) => s.entity === entity && s.key === key);
      const shape = entities[entity as keyof typeof entities].fields;
      return row === undefined ? undefined : (decoded(objectOf(shape), row.value) as Record<string, unknown>)[field];
    },
  };
}

const args = ["input", "records", "createKey"] as const;
const keys: Keys = { owner: "fixtures", next: { Task: { count: 2 } } };
const fields = Object.fromEntries(Object.entries(entities).map(([name, e]) => [name, Object.keys(e.fields)]));

/** The schemas of a fixture's input of `shape` and of the records. */
const typedOf = (shape: Shape): Typed => ({
  args: { input: z.object(shape) },
  entities: { Task: z.object(entities.Task.fields), Settings: z.object(entities.Settings.fields) },
});
const outsideTyped = typedOf({ n: z.number(), title: z.string(), ns: z.array(z.number()) });

const converted = fixtures.map((fixture) => ({
  fixture,
  ir: converter.convert(fixture.f, args, { events: fixture.events ?? [], defined, typed: typedOf(fixture.shape) }),
}));

for (const [i, { fixture, ir }] of converted.entries())
  test(`fixture ${i} (${fixture.op}) converts to IR with ${fixture.op}, which Lean evaluates as TS runs the function on random inputs`, () => {
    if ("unconverted" in ir) assert.fail(`not converted: ${ir.unconverted}`);
    assert.ok(opsOf(ir).has(fixture.op), JSON.stringify(ir));
    const schema = objectOf(fixture.shape);
    fc.assert(
      fc.property(fixture.input, fixture.records, (generated, stored) => {
        const json = JSON.parse(JSON.stringify(generated)) as Json;
        const reads: ReadPart[] = [];
        const records = recordsView(entities, sourceOf(stored, reads));
        const created: string[] = [];
        const createKey = (r: unknown) => {
          created.push(keyOf(r));
          const entity = created.at(-1) ?? "";
          const count = (keys.next[entity]?.count ?? 0) + created.filter((c) => c === entity).length;
          return `${keys.owner}/${entity}-${count}`;
        };
        let ts: { readonly value?: Json } | { readonly issue: "thrown" | "notOnly" };
        try {
          const value = jsonOf(fixture.f({ input: decoded(schema, json), records, createKey } as never));
          ts = value === undefined ? {} : { value: JSON.parse(JSON.stringify(value)) as Json };
        } catch (error) {
          ts = { issue: error instanceof NotOnly ? "notOnly" : "thrown" };
        }
        const evaluated = lean.evaluate(ir, json, stored, keys, fields);
        const { value, issue } = evaluated;
        assert.deepEqual(
          {
            answer: issue === undefined ? (value === undefined ? {} : { value }) : { issue: issue.kind },
            reads: evaluated.reads,
            created: evaluated.created,
          },
          { answer: ts, reads, created },
        );
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
    const ir = converter.convert(f, args, { defined, typed: outsideTyped });
    assert.ok("unconverted" in ir, JSON.stringify(ir));
  });
