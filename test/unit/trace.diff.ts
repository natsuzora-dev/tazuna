import assert from "node:assert/strict";
import { readdirSync } from "node:fs";
import { join } from "node:path";
import { after, test } from "node:test";
import { traceLine } from "../../src/data/trace.generated.ts";
import { readTrace } from "../../src/data/traceFile.ts";
import type { Json } from "../../src/data/values.ts";
import { Lean } from "./lean.ts";

const leanProcess = new Lean();
after(() => leanProcess.close());

function traceFiles(folder: string): string[] {
  return readdirSync(folder, { withFileTypes: true }).flatMap((e) => {
    if (e.name === "node_modules" || e.name.startsWith(".")) return [];
    const path = join(folder, e.name);
    if (e.isDirectory()) return traceFiles(path);
    return e.name.endsWith(".jsonl") && e.name !== "expected.jsonl" ? [path] : [];
  });
}

const lines = ["test", "samples"]
  .flatMap((folder) => traceFiles(join(import.meta.dirname, "../..", folder)))
  .flatMap((file) => readTrace(file).filter((v) => v !== undefined));

type Path = readonly (string | number)[];

/**
 * Returns the paths of the fields of `value`, except the insides of input, payload, and output, which the schema reads
 * as any value.
 */
function fieldPaths(value: Json, path: Path = []): Path[] {
  if (Array.isArray(value)) return value.flatMap((v, i) => [[...path, i], ...fieldPaths(v, [...path, i])]);
  if (value === null || typeof value !== "object") return [];
  return Object.entries(value).flatMap(([k, v]) => [
    [...path, k],
    ...(["input", "payload", "output"].includes(k) ? [] : fieldPaths(v, [...path, k])),
  ]);
}

function rewrite(value: Json, path: Path, f: (v: Json) => Json | undefined): Json {
  const [head, ...rest] = path;
  if (head === undefined) return value;
  const next = (v: Json) => (rest.length === 0 ? f(v) : rewrite(v, rest, f));
  if (Array.isArray(value))
    return value.flatMap((v, i): Json[] => {
      if (i !== head) return [v];
      const w = next(v);
      return w === undefined ? [] : [w];
    });
  if (value === null || typeof value !== "object") return value;
  return Object.fromEntries(
    Object.entries(value).flatMap(([k, v]): [string, Json][] => {
      if (k !== head) return [[k, v]];
      const w = next(v);
      return w === undefined ? [] : [[k, w]];
    }),
  );
}

const fixedTimes = [0, -1, 0.5, 2 ** 53, 9_007_199_254_740_991, -9_007_199_254_740_991, "2026-10-25T09:00:00Z"];

const mutations: Record<string, (line: Json) => Json[]> = {
  fieldRemoved: (line) => fieldPaths(line).map((p) => rewrite(line, p, () => undefined)),
  wrongType: (line) =>
    fieldPaths(line).flatMap((p) => [
      rewrite(line, p, (v) => (typeof v === "string" ? 1 : "x")),
      rewrite(line, p, () => null),
    ]),
  dirFlipped: (line) => [rewrite(line, ["dir"], (v) => (v === "in" ? "out" : "in"))],
  unknownString: (line) =>
    fieldPaths(line).map((p) => rewrite(line, p, (v) => (typeof v === "string" ? "unknownString" : v))),
  time: (line) =>
    [(t: number) => t + 0.5, (t: number) => -t, (t: number) => String(t)].map((f) =>
      rewrite(line, ["time"], (v) => (typeof v === "number" ? f(v) : v)),
    ),
};

test("The generated Zod traceLine and the decoder derived from the Lean TraceLine both reject, or both read to the same value with the same field order, each line of the example traces and snapshots and each mutation of it", (t) => {
  const cases = new Map<string, { kind: string; value: Json }>();
  for (const c of [
    ...lines.map((value) => ({ kind: "example", value })),
    ...Object.entries(mutations).flatMap(([kind, mutate]) => lines.flatMap(mutate).map((value) => ({ kind, value }))),
    ...fixedTimes.map((time) => ({ kind: "fixedTime", value: rewrite(lines[0] ?? null, ["time"], () => time) })),
  ])
    if (!cases.has(JSON.stringify(c.value))) cases.set(JSON.stringify(c.value), c);
  const unique = [...cases.values()];
  const ts = unique.map((c) => {
    const parsed = traceLine.safeParse(c.value);
    return parsed.success ? JSON.stringify(parsed.data) : null;
  });
  const lean = leanProcess.decodeLines(unique.map((c) => c.value)).map((l) => (l === null ? null : JSON.stringify(l)));
  assert.equal(lean.length, unique.length);
  const counts = new Map<string, { read: number; notRead: number }>();
  for (const [i, c] of unique.entries()) {
    const count = counts.get(c.kind) ?? { read: 0, notRead: 0 };
    if (ts[i] === null) count.notRead++;
    else count.read++;
    counts.set(c.kind, count);
  }
  t.diagnostic(`lines ${JSON.stringify(Object.fromEntries(counts))}`);
  assert.deepEqual(
    unique.flatMap((c, i) => (ts[i] === lean[i] ? [] : [{ value: c.value, ts: ts[i], lean: lean[i] }])),
    [],
  );
  for (const [kind, { notRead }] of counts) if (kind !== "example") assert.ok(notRead > 0, kind);
});
