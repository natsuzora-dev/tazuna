import assert from "node:assert/strict";
import { readdirSync } from "node:fs";
import { basename, dirname, join, relative } from "node:path";
import { after, describe, test } from "node:test";
import fc from "fast-check";
import { stringPairs } from "../src/data/binding.ts";
import type { Entry } from "../src/data/pairing.ts";
import type { TraceLine } from "../src/data/trace.generated.ts";
import { isMalformed, parseFileLines } from "../src/data/trace.ts";
import { type Run, readTrace, runStem, sameRun, snapshotPath } from "../src/data/traceFile.ts";
import type { Json } from "../src/data/values.ts";
import type { Placed, ViolationValue } from "../src/data/violation.ts";
import { loadSpec, type Spec } from "../src/load/load.ts";
import { simulateSpec, snapshotsOf } from "../src/sim/spec/simulate.ts";
import { type Compared, verifyLines } from "../src/verify/compare.ts";
import { checkExternal, verifyExternal } from "../src/verify/external.ts";
import { readSnapshotViolations, unknownAfters } from "../src/verify/lines.ts";
import { type Expected, type Folder, pairTraces, type TraceFolder, traceFolderOf } from "../src/verify/pairing.ts";
import { compareSnapshot, pairSnapshots, snapshotFolders, snapshotRuns, withSnapshot } from "../src/verify/snapshot.ts";
import { folders, groupExamples, runExamples } from "./examples.ts";
import { VerifyFunctions } from "./lean/functions.ts";
import { Lean, type VerifyViolation } from "./lean/lean.ts";

const lean = new Lean();
after(() => lean.close());

const verifyRoot = join(import.meta.dirname, "verify");

const examples = groupExamples("verify");

// Run and validation examples too: the resultOf mutations need snapshots with resultOf on `in` lines.
const snapshotExamples = [...examples, ...runExamples(), ...groupExamples("validation")];

const samples = (await loadSpec(join(import.meta.dirname, "../samples/todo/spec"))).spec;

const specs = new Map(
  await Promise.all(snapshotExamples.map(async (root) => [root, (await loadSpec(root)).spec] as const)),
);

const value = ({ kind, definition, line, data }: ViolationValue & Placed) =>
  JSON.parse(JSON.stringify({ kind, definition, line, data })) as VerifyViolation;

const findings = new Map<string, number>();

const bindingsOf = ({ set }: Compared) => set.map((b) => new Map(stringPairs(b)));

interface Case {
  readonly spec: Spec;
  readonly service: string;
  readonly snapshot: readonly (TraceLine | undefined)[];
}

function violationCountOfBoth({ spec, service, snapshot }: Case, trace: readonly unknown[], at: string): number {
  const lines = parseFileLines(trace);
  const compared = verifyLines(spec, service, snapshot, lines);
  const ts = compared.found;
  assert.deepEqual(
    lean.verify(spec, service, snapshot, lines, new VerifyFunctions(spec)),
    { findings: ts.map(value), bindings: bindingsOf(compared).map((b) => Object.fromEntries(b)) },
    at,
  );
  for (const { kind } of ts) findings.set(kind, (findings.get(kind) ?? 0) + 1);
  return ts.length;
}

const snapshotRunsOf = new Map([...specs.values()].map((spec) => [spec, snapshotRuns(spec)]));

const snapshotted = new Map(
  [...specs.values()].map((spec) => [spec, withSnapshot(spec, snapshotRunsOf.get(spec) ?? [])]),
);

const snapshotOf = (spec: Spec, run: Run) => snapshotted.get(spec)?.some((s) => sameRun(s, run)) === true;

const snapshots = [...specs].flatMap(([root, spec]) =>
  (snapshotted.get(spec) ?? [])
    .filter((s) => spec.services.get(s.service)?.definition.external !== true)
    .map((s) => ({
      spec,
      service: s.runner,
      name: runStem(s),
      label: `${relative(import.meta.dirname, root)}/${s.service}/${runStem(s)}`,
      read: readSnapshotViolations(snapshotPath(spec, s)),
    })),
);

/** The snapshots that verify compares. */
const bases = snapshots.filter((s) => s.read.violations.length === 0).map((s) => ({ ...s, snapshot: s.read.lines }));

const readable = snapshots.filter((s) => !s.read.violations.some((p) => p.kind === "Uncomparable.lineSchema"));

function aftersOfBoth(snapshot: readonly (TraceLine | undefined)[], at: string): number {
  const ts = unknownAfters(snapshot).map(value);
  assert.deepEqual(lean.afters(snapshot), ts, at);
  return ts.length;
}

type Pick3 = readonly [number, number, number];
type Line = { [key: string]: Json };

const pick = <T>(items: readonly T[], k: number): T | undefined => items[k % Math.max(items.length, 1)];

function leaves(value: Json, path: (string | number)[] = []): (string | number)[][] {
  if (Array.isArray(value)) return value.flatMap((v, i) => leaves(v, [...path, i]));
  if (value !== null && typeof value === "object")
    return Object.entries(value).flatMap(([k, v]) => leaves(v, [...path, k]));
  return [path];
}

function update(value: Json, path: readonly (string | number)[], f: (leaf: Json) => Json): Json {
  const [head, ...rest] = path;
  if (head === undefined) return f(value);
  if (Array.isArray(value)) return value.map((v, i) => (i === head ? update(v, rest, f) : v));
  if (value !== null && typeof value === "object")
    return Object.fromEntries(Object.entries(value).map(([k, v]) => [k, k === head ? update(v, rest, f) : v]));
  return value;
}

const contentKeys = ["input", "payload", "answer"] as const;
const strings = (lines: readonly Line[]) =>
  lines
    .flatMap((l) => leaves(l).flatMap((p) => p.reduce<Json>((v, k) => (v as never)[k], l)))
    .filter((v): v is string => typeof v === "string");

/** The trace mutations. Some of them, field order and +09:00, are not differences. */
const mutations: Record<string, (lines: Line[], k: Pick3) => Line[]> = {
  drop: (lines, [a]) => lines.toSpliced(a % Math.max(lines.length, 1), 1),
  duplicate: (lines, [a]) => {
    const i = a % Math.max(lines.length, 1);
    const line = lines[i];
    return line === undefined ? lines : lines.toSpliced(i, 0, structuredClone(line));
  },
  swap: (lines, [a, b]) => {
    const [i, j] = [a % Math.max(lines.length, 1), b % Math.max(lines.length, 1)];
    const copy = [...lines];
    [copy[i], copy[j]] = [copy[j] as Line, copy[i] as Line];
    return copy;
  },
  swapNext: (lines, [a]) => {
    const i = a % Math.max(lines.length - 1, 1);
    const copy = [...lines];
    if (copy[i + 1] !== undefined) [copy[i], copy[i + 1]] = [copy[i + 1] as Line, copy[i] as Line];
    return copy;
  },
  value: (lines, [a, b, c]) =>
    lines.map((l, i) => {
      if (i !== a % lines.length) return l;
      const key = contentKeys.find((k) => k in l);
      if (key === undefined) return l;
      const path = pick(leaves(l[key] as Json), b);
      if (path === undefined) return l;
      const others = strings(lines);
      return {
        ...l,
        [key]: update(l[key] as Json, path, (v) =>
          typeof v === "number"
            ? v + 1 + (c % 3)
            : typeof v === "string"
              ? c % 2 === 0
                ? (pick(others, c) ?? `${v}x`)
                : `${v}x`
              : typeof v === "boolean"
                ? !v
                : v,
        ),
      };
    }),
  reorder: (lines, [a, b]) =>
    lines.map((l, i) => {
      if (i !== a % lines.length) return l;
      const key = contentKeys.find((k) => k in l);
      if (key === undefined) return l;
      const reversed = (v: Json): Json =>
        Array.isArray(v)
          ? b % 2 === 0
            ? v.map(reversed).toReversed()
            : v.map(reversed)
          : v !== null && typeof v === "object"
            ? Object.fromEntries(
                Object.entries(v)
                  .toReversed()
                  .map(([k, x]) => [k, reversed(x)]),
              )
            : v;
      return { ...l, [key]: reversed(l[key] as Json) };
    }),
  removeField: (lines, [a, b]) =>
    lines.map((l, i) => {
      if (i !== a % lines.length) return l;
      const key = contentKeys.find((k) => k in l);
      const value = key === undefined ? undefined : l[key];
      if (key === undefined || value === null || typeof value !== "object" || Array.isArray(value)) return l;
      const field = pick(Object.keys(value), b);
      return field === undefined
        ? l
        : { ...l, [key]: Object.fromEntries(Object.entries(value).filter(([k]) => k !== field)) };
    }),
  id: (lines, [a, b, c]) => {
    const ids = lines.flatMap((l) => (typeof l["id"] === "string" ? [l["id"]] : []));
    return lines.map((l, i) => {
      if (i !== a % lines.length) return l;
      const field = pick(["id", "to", "resultOf"], b) as string;
      if (!(field in l) && field !== "id") return l;
      return { ...l, [field]: c % 3 === 0 ? `impl-${c}` : (pick(ids, c) ?? "x") };
    });
  },
  renameIds: (lines, [a]) => {
    const rename = (id: Json) => (typeof id === "string" ? `${id}~${a % 5}` : id);
    return lines.map((l) => ({
      ...l,
      ...("id" in l ? { id: rename(l["id"] as Json) } : {}),
      ...("to" in l ? { to: rename(l["to"] as Json) } : {}),
      ...("resultOf" in l ? { resultOf: rename(l["resultOf"] as Json) } : {}),
    }));
  },
  time: (lines, [a, b]) =>
    lines.map((l, i) => {
      if (i !== a % lines.length) return l;
      const instant = Temporal.Instant.from(l["time"] as string);
      const time =
        b % 3 === 0
          ? instant.toZonedDateTimeISO("+09:00").toString({ timeZoneName: "never" })
          : instant.add({ milliseconds: b % 3 === 1 ? 1000 : -1 }).toString();
      return { ...l, time };
    }),
  answer: (lines, [a, b]) =>
    lines.map((l, i) => {
      if (i !== a % lines.length || l["type"] !== "answer") return l;
      return {
        ...l,
        answer: pick(
          [
            { result: "accepted" },
            { result: "rejected", rejection: { kind: "requires", reason: "r" } },
            { result: "rejected", rejection: { kind: "not-found" } },
            { result: "rejected", rejection: { kind: "unavailable" } },
            { result: "fulfilled", output: {} },
          ],
          b,
        ) as Json,
      };
    }),
  resultOf: (lines, [a, b]) => {
    const ids = lines.flatMap((l) => (typeof l["id"] === "string" ? [l["id"]] : []));
    const targets = lines.flatMap((l, i) => ("resultOf" in l ? [i] : []));
    const target = pick(targets, a);
    return lines.map((l, i) =>
      i !== target
        ? l
        : b % 4 === 0
          ? Object.fromEntries(Object.entries(l).filter(([k]) => k !== "resultOf"))
          : { ...l, resultOf: pick(ids, b) ?? "x" },
    );
  },
  dir: (lines, [a]) =>
    lines.map((l, i) => (i !== a % lines.length ? l : { ...l, dir: l["dir"] === "in" ? "out" : "in" })),
  malformed: (lines, [a]) =>
    lines.map((l, i) =>
      i !== a % lines.length ? l : Object.fromEntries(Object.entries(l).filter(([k]) => k !== "type")),
    ),
  insertMalformed: (lines, [a, b]) => {
    const line = lines[a % Math.max(lines.length, 1)];
    return line === undefined
      ? lines
      : lines.toSpliced(
          b % (lines.length + 1),
          0,
          Object.fromEntries(Object.entries(line).filter(([k]) => k !== "type")),
        );
  },
  stripOrder: (lines) => lines.map(({ after: _after, created: _created, ...rest }) => rest),
};

const runs = Number(process.env["TAZUNA_LEAN_VERIFY_RUNS"] ?? 1000);

/** The bases whose snapshots have resultOf, which get their own run because few snapshots have it. */
const withResultOf = bases.filter((b) => b.snapshot.some((l) => l?.dir === "in" && "resultOf" in l));

describe("Content comparison", () => {
  for (const root of examples) {
    const spec = specs.get(root) as Spec;
    for (const file of folders(join(root, "traces")).flatMap((d) =>
      readdirSync(d)
        .filter((f) => f.endsWith(".jsonl"))
        .map((f) => join(d, f)),
    )) {
      const service = basename(dirname(file));
      const name = basename(file, ".jsonl");
      if (!spec.services.has(service) || spec.services.get(service)?.definition.external === true) continue;
      const run = snapshotted.get(spec)?.find((r) => r.service === service && runStem(r) === name);
      if (run === undefined) continue;
      const snapshot = readSnapshotViolations(snapshotPath(spec, run));
      if (snapshot.violations.length > 0) continue;
      test(`${relative(verifyRoot, file)}: TS and Lean find the same comparison violations`, () => {
        violationCountOfBoth({ spec, service: run.runner, snapshot: snapshot.lines }, readTrace(file), file);
      });
    }
  }

  test("The snapshots that verify does not compare are those of the examples with an unreadable line or an after that names no line", () => {
    assert.deepEqual(
      snapshots.filter((s) => s.read.violations.length > 0).map((s) => s.label),
      [
        "verify/uncomparable/lines/unknown-after/todo/addOneUnknownAfter",
        "verify/uncomparable/snapshot/line-schema/todo/addOneCut",
      ],
    );
  });

  test("TS and Lean find the same comparison violations when each snapshot serves as the implementation trace", () => {
    for (const base of bases) violationCountOfBoth(base, base.snapshot, base.label);
  });

  test("TS and Lean find the same unknownAfter violations in the snapshots", () => {
    assert.ok(readable.reduce((n, s) => n + aftersOfBoth(s.read.lines, s.label), 0) > 0);
  });

  test("TS and Lean find the same comparison violations for mutated traces", (t) => {
    const counts = new Map<string, number>();
    fc.assert(
      fc.property(
        fc.nat(bases.length - 1),
        fc.array(fc.tuple(fc.constantFrom(...Object.keys(mutations), "blank"), fc.nat(), fc.nat(), fc.nat()), {
          minLength: 1,
          maxLength: 5,
        }),
        (k, ops) => {
          const base = bases[k] as (typeof bases)[number];
          let lines = structuredClone(base.snapshot.filter((l) => l !== undefined)) as unknown as Line[];
          const blanks: number[] = [];
          for (const [op, a, b, c] of ops)
            if (op === "blank") blanks.push(a);
            else if (lines.length > 0) lines = mutations[op]?.(lines, [a, b, c]) ?? lines;
          const trace = blanks.reduce<(Line | undefined)[]>(
            (ls, a) => ls.toSpliced(a % (ls.length + 1), 0, undefined),
            lines,
          );
          const kind =
            violationCountOfBoth(base, trace, `${base.label} ${JSON.stringify(ops)}`) === 0 ? "none" : "some";
          counts.set(kind, (counts.get(kind) ?? 0) + 1);
        },
      ),
      { numRuns: runs },
    );
    t.diagnostic(`traces ${JSON.stringify(Object.fromEntries(counts))}`);
    t.diagnostic(`findings ${JSON.stringify(Object.fromEntries([...findings].sort()))}`);
  });

  test("TS and Lean find the same violations when one key of a trace with thirty equal tasks changes", () => {
    const own = samples.scenarios.find((s) => s.service === "todo");
    assert.ok(own !== undefined);
    const lines = Array.from({ length: 30 }, (_, i) => ({
      type: "request" as const,
      kind: "command" as const,
      target: { service: "todo", name: "addTask" },
      input: { value: { taskId: `task-${i + 1}`, title: "Buy milk" }, holes: [] },
    }));
    const snapshot = snapshotsOf(simulateSpec(samples, { ...own.definition.scenario, lines, expectations: [] })).get(
      "todo",
    );
    assert.ok(snapshot !== undefined);
    const base: Case = { spec: samples, service: "todo", snapshot };
    const label = "thirty equal tasks";
    const trace = structuredClone(base.snapshot) as unknown as Line[];
    const changed = trace.findIndex((l) => l?.["type"] === "event" && l["name"] === "taskAdded");
    trace[changed] = { ...trace[changed], payload: { taskId: "event" } } as Line;
    assert.ok(violationCountOfBoth(base, trace, label) > 0);
  });

  const caseOf = (folder: string, service: string, snapshot: readonly Line[]): Case => {
    const spec = [...specs].find(([root]) => root.endsWith(folder))?.[1];
    assert.ok(spec !== undefined, folder);
    return { spec, service, snapshot: snapshot as unknown as TraceLine[] };
  };
  const at = "2026-10-25T00:00:00Z";
  const addTask = (id: string, n: number): Line => ({
    time: at,
    dir: "in",
    type: "command",
    id,
    name: "addTask",
    input: { taskId: `task-${n}`, title: "Buy milk" },
  });
  const countChanged = (id: string, more: Line = {}): Line => ({
    time: at,
    dir: "out",
    type: "event",
    id,
    name: "taskCountChanged",
    payload: { count: 1 },
    ...more,
  });
  const nextDay = (id: string): Line => ({
    time: at,
    dir: "out",
    type: "query",
    id,
    name: "calendar.nextDay",
    input: { from: at },
  });

  test("TS and Lean pair equal out lines in file order, and by their resultOf", () => {
    const inOrder = caseOf("compare/order", "todo", [
      addTask("addTask#1", 1),
      countChanged("taskCountChanged#1"),
      nextDay("calendar.nextDay#1"),
      countChanged("taskCountChanged#2"),
    ]);
    assert.equal(
      violationCountOfBoth(
        inOrder,
        [addTask("addTask#1", 1), nextDay("r1"), countChanged("e1"), countChanged("e2")],
        "file order",
      ),
      0,
    );
    const resultOf = caseOf("compare/order", "todo", [
      addTask("addTask#1", 1),
      addTask("addTask#2", 2),
      countChanged("taskCountChanged#1", { resultOf: "addTask#2" }),
      countChanged("taskCountChanged#2", { resultOf: "addTask#1" }),
    ]);
    assert.equal(
      violationCountOfBoth(
        resultOf,
        [
          addTask("addTask#1", 1),
          addTask("addTask#2", 2),
          countChanged("e1", { resultOf: "addTask#1" }),
          countChanged("e2", { resultOf: "addTask#2" }),
        ],
        "resultOf",
      ),
      0,
    );
  });

  const seenIds = (id: string): Line => ({ time: at, dir: "in", type: "query", id, name: "seenIds", input: {} });
  const answer = (id: string, to: string, ids: string[], listed: string[], more: Line = {}): Line => ({
    time: at,
    dir: "out",
    type: "answer",
    id,
    to,
    answer: { result: "fulfilled", output: { repeated: [], none: [], ids, listed } },
    ...more,
  });

  test("TS and Lean keep the keys of a bag that one group creates open until a later group names one key", () => {
    const created = caseOf("compare/created-keys", "todo", [
      seenIds("seenIds#1"),
      answer("answer#1", "seenIds#1", ["Seen-1", "Seen-2"], [], { created: ["Seen-1", "Seen-2"] }),
      seenIds("seenIds#2"),
      answer("answer#2", "seenIds#2", ["Seen-1", "Seen-2"], ["Seen-1"]),
    ]);
    const trace = [
      seenIds("seenIds#1"),
      answer("a1", "seenIds#1", ["x", "y"], []),
      seenIds("seenIds#2"),
      answer("a2", "seenIds#2", ["x", "y"], ["y"]),
    ];
    assert.equal(violationCountOfBoth(created, trace, "named later"), 0);
    const bindings = bindingsOf(verifyLines(created.spec, "todo", created.snapshot, parseFileLines(trace)));
    assert.deepEqual(
      bindings.map((b) => [b.get("Seen-1"), b.get("Seen-2")]),
      [["y", "x"]],
    );
  });

  test("TS and Lean end with every binding that agrees with the trace: bag counts decide one, and symmetric links keep two until a later line decides", () => {
    const ended = (example: string, name: string) => {
      const base = bases.find((b) => b.spec === specs.get(join(verifyRoot, example)) && b.name === name);
      assert.ok(base !== undefined, name);
      const trace = readTrace(join(verifyRoot, example, "traces", base.service, `${name}.jsonl`));
      assert.equal(violationCountOfBoth(base, trace, name), 0, name);
      return bindingsOf(verifyLines(base.spec, base.service, base.snapshot, parseFileLines(trace)));
    };
    const keys = (example: string, name: string, ...snapshotKeys: string[]) =>
      ended(example, name).map((b) => snapshotKeys.map((k) => b.get(k)));
    assert.deepEqual(keys("mismatch/compare/created-keys", "seenMultiplicity", "todo/Seen-1", "todo/Seen-2"), [
      ["y", "x"],
    ]);
    assert.deepEqual(keys("mismatch/compare/symmetric-keys", "draftTwo", "screens/Draft-1", "screens/Draft-2"), [
      ["n2", "n1"],
      ["n1", "n2"],
    ]);
    assert.deepEqual(keys("mismatch/compare/symmetric-keys", "draftTwoPointed", "screens/Draft-1", "screens/Draft-2"), [
      ["n2", "n1"],
    ]);
  });

  test("TS and Lean report an implementation that gives a created key the value of an existing key of its entity", () => {
    const created = caseOf("compare/created-keys", "todo", [
      seenIds("seenIds#1"),
      answer("answer#1", "seenIds#1", ["Seen-1"], [], { created: ["Seen-1"] }),
      seenIds("seenIds#2"),
      answer("answer#2", "seenIds#2", ["Seen-1", "Seen-2"], ["Seen-2"], { created: ["Seen-2"] }),
    ]);
    const trace = [
      seenIds("seenIds#1"),
      answer("a1", "seenIds#1", ["x"], []),
      seenIds("seenIds#2"),
      answer("a2", "seenIds#2", ["x", "x"], ["x"]),
    ];
    assert.ok(violationCountOfBoth(created, trace, "reused key") > 0);
    const found = verifyLines(created.spec, created.service, created.snapshot, parseFileLines(trace)).found;
    assert.deepEqual(
      found.map((f) => f.kind),
      ["Mismatch.output"],
    );
  });

  test("TS and Lean accept a created key whose value is a string of another domain: another entity's key or a request id", () => {
    const snapshot = specs.get(join(verifyRoot, "mismatch/compare/created-keys"));
    assert.ok(snapshot !== undefined);
    const seenOnce = bases.find((b) => b.spec === snapshot && b.name === "seenOnce");
    assert.ok(seenOnce !== undefined);
    for (const value of ["task-1", "addTask#1"]) {
      const trace = JSON.parse(
        JSON.stringify(
          seenOnce.snapshot.flatMap((l) => (l === undefined ? [] : [{ ...l, after: undefined, created: undefined }])),
        ).replaceAll("todo/Seen-1", value),
      ) as Line[];
      assert.equal(violationCountOfBoth(seenOnce, trace, value), 0, value);
    }
  });

  test("TS and Lean pair equal lines of one group by their time and by their after order", () => {
    const later = "2026-10-25T01:00:00Z";
    const byTime = caseOf("compare/order", "todo", [
      addTask("addTask#1", 1),
      nextDay("calendar.nextDay#1"),
      { ...nextDay("calendar.nextDay#2"), time: later },
    ]);
    const trace = [addTask("addTask#1", 1), { ...nextDay("r2"), time: later }, nextDay("r1")];
    assert.equal(violationCountOfBoth(byTime, trace, "time"), 0);
    const bindings = bindingsOf(verifyLines(byTime.spec, "todo", byTime.snapshot, parseFileLines(trace)));
    assert.deepEqual(
      bindings.map((b) => [b.get("calendar.nextDay#1"), b.get("calendar.nextDay#2")]),
      [["r1", "r2"]],
    );
    const byAfter = caseOf("compare/order", "todo", [
      addTask("addTask#1", 1),
      nextDay("calendar.nextDay#1"),
      countChanged("taskCountChanged#1", { after: ["calendar.nextDay#1"] }),
      countChanged("taskCountChanged#2"),
    ]);
    assert.equal(
      violationCountOfBoth(
        byAfter,
        [addTask("addTask#1", 1), countChanged("e1"), nextDay("r1"), countChanged("e2")],
        "after",
      ),
      0,
    );
  });

  test("TS and Lean report an answer to one of equal requests as ambiguous when the snapshot answers them differently", () => {
    const dayAnswer = (to: string, day: string, n = to): Line => ({
      time: at,
      dir: "in",
      type: "answer",
      id: `answer:${n}`,
      to,
      answer: { result: "fulfilled", output: { day } },
    });
    const snapshotOf = (second: string) =>
      caseOf("compare/order", "todo", [
        addTask("addTask#1", 1),
        nextDay("calendar.nextDay#1"),
        nextDay("calendar.nextDay#2"),
        dayAnswer("calendar.nextDay#1", "2026-10-26T00:00:00Z"),
        dayAnswer("calendar.nextDay#2", second),
      ]);
    const trace = (second: string) => [
      addTask("addTask#1", 1),
      nextDay("r1"),
      nextDay("r2"),
      dayAnswer("r1", "2026-10-26T00:00:00Z", "calendar.nextDay#1"),
      dayAnswer("r2", second, "calendar.nextDay#2"),
    ];
    assert.equal(violationCountOfBoth(snapshotOf("2026-10-26T00:00:00Z"), trace("2026-10-26T00:00:00Z"), "alike"), 0);
    const differently = snapshotOf("2026-10-27T00:00:00Z");
    assert.ok(violationCountOfBoth(differently, trace("2026-10-27T00:00:00Z"), "differently") > 0);
    const { found } = verifyLines(
      differently.spec,
      "todo",
      differently.snapshot,
      parseFileLines(trace("2026-10-27T00:00:00Z")),
    );
    assert.deepEqual(
      found.map((f) => [f.kind, f.line, f.data]),
      [
        [
          "Uncomparable.ambiguous",
          4,
          { subject: { type: "answer", to: "calendar.nextDay#1" }, snapshotLine: 4, candidates: [2, 3] },
        ],
      ],
    );
  });

  test("TS and Lean find the same comparison violations for traces with a mutated resultOf on an in event line", () => {
    fc.assert(
      fc.property(
        fc.nat(withResultOf.length - 1),
        fc.array(fc.tuple(fc.constantFrom("resultOf", "id", "swapNext", "drop"), fc.nat(), fc.nat(), fc.nat()), {
          minLength: 1,
          maxLength: 3,
        }),
        (k, ops) => {
          const base = withResultOf[k] as (typeof withResultOf)[number];
          let lines = structuredClone(base.snapshot.filter((l) => l !== undefined)) as unknown as Line[];
          for (const [op, a, b, c] of ops) if (lines.length > 0) lines = mutations[op]?.(lines, [a, b, c]) ?? lines;
          violationCountOfBoth(base, lines, `${base.label} ${JSON.stringify(ops)}`);
        },
      ),
      { numRuns: Math.ceil(runs / 5) },
    );
  });

  test("TS and Lean find the same unknownAfter violations for snapshots with a mutated after and id", () => {
    fc.assert(
      fc.property(
        fc.nat(bases.length - 1),
        fc.array(fc.tuple(fc.constantFrom("after", "id", "drop", "swapNext"), fc.nat(), fc.nat(), fc.nat()), {
          minLength: 1,
          maxLength: 3,
        }),
        (k, ops) => {
          const base = bases[k] as (typeof bases)[number];
          let lines = structuredClone(base.snapshot.filter((l) => l !== undefined)) as unknown as Line[];
          for (const [op, a, b, c] of ops)
            if (lines.length > 0)
              lines =
                op === "after"
                  ? lines.map((l, i) =>
                      i !== a % lines.length
                        ? l
                        : {
                            ...l,
                            after: [pick(strings(lines), b) ?? "x", ...((l["after"] as Json[]) ?? [])].slice(
                              0,
                              1 + (c % 2),
                            ),
                          },
                    )
                  : (mutations[op]?.(lines, [a, b, c]) ?? lines);
          aftersOfBoth(lines as unknown as TraceLine[], `${base.label} ${JSON.stringify(ops)}`);
        },
      ),
      { numRuns: Math.ceil(runs / 5) },
    );
  });
});

const externalFindings = new Map<string, number>();

function externalFindingsOfBoth(
  { spec, service }: { readonly spec: Spec; readonly service: string },
  values: readonly unknown[],
  at: string,
): number {
  const trace = parseFileLines(values);
  const ts = checkExternal(spec, service, trace).found.map(value);
  assert.deepEqual(lean.checkExternal(spec, service, trace), ts, at);
  const verified = new Set(verifyExternal(spec, service, trace).map((v) => JSON.stringify(value(v))));
  assert.deepEqual(
    ts.filter((v) => !verified.has(JSON.stringify(v))),
    [],
    `verifyExternal reports what checkExternal finds for ${at}`,
  );
  for (const { kind } of ts) externalFindings.set(kind, (externalFindings.get(kind) ?? 0) + 1);
  return ts.length;
}

const externalTraces = [...specs].flatMap(([root, spec]) =>
  folders(join(root, "traces")).flatMap((folder) => {
    const service = basename(folder);
    if (spec.services.get(service)?.definition.external !== true) return [];
    const names = spec.structure.definitions.filter((d) => d.service === service).map((d) => d.name);
    return readdirSync(folder)
      .filter((f) => f.endsWith(".jsonl"))
      .map((f) => ({
        spec,
        service,
        names,
        label: relative(import.meta.dirname, join(folder, f)),
        values: readTrace(join(folder, f)),
      }));
  }),
);

type FileValue = Json | undefined;

const isLine = (v: FileValue): v is Line => v !== null && typeof v === "object" && !Array.isArray(v);

const rewrite =
  (picks: (l: Line) => boolean, f: (l: Line, ids: readonly string[], names: readonly string[], b: number) => Line) =>
  (values: FileValue[], names: readonly string[], [a, b]: Pick3): FileValue[] => {
    const ids = values.flatMap((l) => (isLine(l) && typeof l["id"] === "string" ? [l["id"]] : []));
    const target = pick(
      values.flatMap((l, i) => (isLine(l) && picks(l) ? [i] : [])),
      a,
    );
    return values.map((l, i) => (i === target && isLine(l) ? f(l, ids, names, b) : l));
  };

const answerResult = (l: Line) => (isLine(l["answer"]) ? l["answer"]["result"] : undefined);

const externalMutations: Record<string, (values: FileValue[], names: readonly string[], k: Pick3) => FileValue[]> = {
  rename: rewrite(
    (l) => typeof l["name"] === "string",
    (l, _ids, names, b) => ({ ...l, name: pick([...names, `${l["name"]}x`], b) as string }),
  ),
  to: rewrite(
    (l) => typeof l["to"] === "string",
    (l, ids, _names, b) => ({ ...l, to: pick([...ids, "x"], b) as string }),
  ),
  resultOf: rewrite(
    (l) => l["type"] === "event",
    (l, ids, _names, b) =>
      b % 3 === 0
        ? Object.fromEntries(Object.entries(l).filter(([k]) => k !== "resultOf"))
        : { ...l, resultOf: pick([...ids, "x"], b) as string },
  ),
  drop: (values, _names, [a]) => values.toSpliced(a % Math.max(values.length, 1), 1),
  flip: rewrite(
    (l) => answerResult(l) === "accepted" || answerResult(l) === "rejected" || answerResult(l) === "fulfilled",
    (l) => ({
      ...l,
      answer:
        answerResult(l) === "accepted"
          ? { result: "rejected", rejection: { kind: "unavailable" } }
          : answerResult(l) === "rejected"
            ? { result: "fulfilled", output: {} }
            : { result: "accepted" },
    }),
  ),
  reuseId: rewrite(
    (l) => l["dir"] === "in" && (l["type"] === "command" || l["type"] === "query"),
    (l, ids, _names, b) => ({ ...l, id: pick(ids, b) as string }),
  ),
  dropId: rewrite(
    (l) => l["dir"] === "in" && (l["type"] === "command" || l["type"] === "query") && "id" in l,
    (l) => Object.fromEntries(Object.entries(l).filter(([k]) => k !== "id")),
  ),
  blank: (values, _names, [a, b]) => {
    const malformed = parseFileLines(values).flatMap((l, i) => (isMalformed(l) ? [i] : []));
    const at = b % 2 === 0 ? pick(malformed, a) : undefined;
    return values.toSpliced(at ?? a % (values.length + 1), 0, undefined);
  },
  insertMalformed: (values, _names, [a, b]) =>
    values.toSpliced(a % (values.length + 1), 0, pick(["booked 2026-10-26", { dir: "out" }], b) as Json),
};

describe("External service trace check", () => {
  for (const base of externalTraces)
    test(`${base.label}: TS and Lean find the same checkExternal violations`, () => {
      externalFindingsOfBoth(base, base.values, base.label);
    });

  test("TS and Lean find the same checkExternal violations for mutated external service traces", (t) => {
    const counts = new Map<string, number>();
    fc.assert(
      fc.property(
        fc.nat(externalTraces.length - 1),
        fc.array(fc.tuple(fc.constantFrom(...Object.keys(externalMutations)), fc.nat(), fc.nat(), fc.nat()), {
          minLength: 1,
          maxLength: 5,
        }),
        (k, ops) => {
          const base = externalTraces[k] as (typeof externalTraces)[number];
          let values = structuredClone(base.values);
          for (const [op, a, b, c] of ops) values = externalMutations[op]?.(values, base.names, [a, b, c]) ?? values;
          const kind =
            externalFindingsOfBoth(base, values, `${base.label} ${JSON.stringify(ops)}`) === 0 ? "none" : "some";
          counts.set(kind, (counts.get(kind) ?? 0) + 1);
        },
      ),
      { numRuns: runs },
    );
    t.diagnostic(`traces ${JSON.stringify(Object.fromEntries(counts))}`);
    t.diagnostic(`findings ${JSON.stringify(Object.fromEntries([...externalFindings].sort()))}`);
  });
});

function pairBoth(spec: Spec, expected: readonly Expected[], folder: TraceFolder, at: string): number {
  const services = spec.structure.services.map(({ name, external }) => ({ name, external }));
  const { compare, contract, violations } = pairTraces(services, expected, folder);
  const fromLean = lean.pair({ services, expected, others: folder.others, folders: folder.folders });
  assert.deepEqual(fromLean, JSON.parse(JSON.stringify({ compare, contract, findings: violations })), at);
  return violations.length;
}

const withSnapshots = (spec: Spec): Expected[] =>
  (snapshotRunsOf.get(spec) ?? []).map((run) => ({ run, compared: snapshotOf(spec, run) }));

const entryKinds = ["file", "folder", "other"] as const;

const entryArbitrary = fc.tuple(fc.nat(), fc.nat(entryKinds.length - 1), fc.boolean());

function entriesOf(names: readonly string[], entries: readonly (readonly [number, number, boolean])[]): Entry[] {
  const entryName = (n: number, jsonl: boolean) => `${names[n % names.length]}${jsonl ? ".jsonl" : ".txt"}`;
  return [
    ...new Map(
      entries.map(([n, kind, jsonl]) => [
        entryName(n, jsonl),
        { name: entryName(n, jsonl), kind: entryKinds[kind] as Entry["kind"] },
      ]),
    ).values(),
  ];
}

const randomScenarios = (spec: Spec, compared: readonly boolean[]): Expected[] =>
  (snapshotRunsOf.get(spec) ?? []).map((run, i) => ({ run, compared: compared[i] ?? true }));

const namesOf = (spec: Spec) => [...(snapshotRunsOf.get(spec) ?? []).map(runStem), "removed"];

describe("Pairing traces with snapshots", () => {
  for (const root of examples)
    test(`${relative(verifyRoot, root)}: TS and Lean find the same violations in pairing traces with snapshots`, () => {
      const spec = specs.get(root) as Spec;
      pairBoth(spec, withSnapshots(spec), traceFolderOf(join(root, "traces")), root);
    });

  test("TS and Lean find the same pairing violations for random trace folders", () => {
    const all = [...specs.values()];
    fc.assert(
      fc.property(
        fc.nat(all.length - 1),
        fc.array(fc.boolean(), { maxLength: 8 }),
        fc.array(fc.nat(), { maxLength: 2 }),
        fc.uniqueArray(fc.tuple(fc.nat(), fc.array(entryArbitrary, { maxLength: 5 })), {
          maxLength: 4,
          selector: ([a]) => a % 8,
        }),
        (k, compared, others, folders) => {
          const spec = all[k] as Spec;
          const services = [...spec.services.keys(), "other"];
          const names = namesOf(spec);
          const scenarios = randomScenarios(spec, compared);
          const folder: TraceFolder = {
            others: others.map((n) => `${names[n % names.length]}.jsonl`),
            folders: [
              ...new Map(folders.map(([a, entries]) => [services[a % services.length] as string, entries])).entries(),
            ].map(([service, entries]) => ({ service, entries: entriesOf(names, entries) })),
          };
          pairBoth(spec, scenarios, folder, JSON.stringify({ scenarios, folder }));
        },
      ),
      { numRuns: 300 },
    );
  });
});

function pairSnapshotsBoth(
  services: readonly string[],
  expected: readonly Expected[],
  folders: readonly Folder[],
  at: string,
): number {
  const { compare, violations } = pairSnapshots(services, expected, folders);
  assert.deepEqual(
    lean.pairSnapshots({ services, expected, folders }),
    JSON.parse(JSON.stringify({ compare, findings: violations })),
    at,
  );
  return violations.length;
}

describe("Pairing scenarios with snapshot files", () => {
  test("TS and Lean find the same pairing violations for the scenarios and snapshot files of the examples", () => {
    let found = 0;
    for (const [root, spec] of specs) {
      const { services, folders } = snapshotFolders(spec);
      found += pairSnapshotsBoth(
        services,
        withSnapshots(spec).map((e) => ({ ...e, compared: true })),
        folders,
        root,
      );
    }
    assert.ok(found > 0);
  });

  test("TS and Lean find the same pairing violations for random snapshot folders", () => {
    const all = [...specs.values()];
    fc.assert(
      fc.property(
        fc.nat(all.length - 1),
        fc.array(fc.boolean(), { maxLength: 8 }),
        fc.array(fc.option(fc.array(entryArbitrary, { maxLength: 5 })), { maxLength: 4 }),
        (k, compared, entries) => {
          const spec = all[k] as Spec;
          const services = [...spec.services.keys(), "other"];
          const scenarios = randomScenarios(spec, compared);
          const folders = services.flatMap((service, i) => {
            const e = entries[i];
            return e === undefined || e === null ? [] : [{ service, entries: entriesOf(namesOf(spec), e) }];
          });
          pairSnapshotsBoth(services, scenarios, folders, JSON.stringify({ scenarios, folders }));
        },
      ),
      { numRuns: 300 },
    );
  });
});

const snapshotFiles = bases.map(({ label, read }) => ({ label, lines: read.values }));

function snapshotFindingsOfBoth(snapshot: readonly (Json | undefined)[], run: readonly Json[], at: string): number {
  const ts = compareSnapshot(snapshot, run);
  assert.deepEqual(lean.compareSnapshot(snapshot, run), ts === undefined ? null : value(ts), at);
  return ts === undefined ? 0 : 1;
}

const defined = (lines: readonly (Json | undefined)[]): Json[] => lines.filter((l) => l !== undefined);

const lineMutations: Record<string, (lines: (Json | undefined)[], k: Pick3) => (Json | undefined)[]> = {
  value: (lines, [a, b, c]) =>
    lines.map((l, i) => {
      if (i !== a % lines.length || l === undefined) return l;
      const path = pick(leaves(l), b);
      return path === undefined
        ? l
        : update(l, path, (v) =>
            typeof v === "number" ? v + 1 + (c % 3) : typeof v === "string" ? `${v}x` : typeof v === "boolean" ? !v : v,
          );
    }),
  reorder: (lines, [a]) =>
    lines.map((l, i) =>
      i !== a % lines.length || l === null || typeof l !== "object" || Array.isArray(l)
        ? l
        : Object.fromEntries(Object.entries(l).toReversed()),
    ),
  drop: (lines, [a]) => lines.toSpliced(a % Math.max(lines.length, 1), 1),
  repeat: (lines, [a]) => {
    const i = a % Math.max(lines.length, 1);
    return i < lines.length ? lines.toSpliced(i, 0, structuredClone(lines[i])) : lines;
  },
};

describe("Comparing runs with snapshots", () => {
  test("TS and Lean find the same violations when each example snapshot is compared with a run of the same lines", () => {
    for (const { label, lines } of snapshotFiles) snapshotFindingsOfBoth(lines, defined(lines), label);
  });

  test("TS and Lean find the same violations when lines of the run, the snapshot, or both are mutated, removed, or repeated, and blank lines are added to the snapshot", (t) => {
    const counts = new Map<string, number>();
    fc.assert(
      fc.property(
        fc.nat(snapshotFiles.length - 1),
        fc.array(
          fc.tuple(
            fc.constantFrom(...Object.keys(lineMutations), "blank"),
            fc.constantFrom("snapshot", "run", "both"),
            fc.nat(),
            fc.nat(),
            fc.nat(),
          ),
          { minLength: 1, maxLength: 4 },
        ),
        (k, ops) => {
          const base = snapshotFiles[k] as (typeof snapshotFiles)[number];
          let snapshot = structuredClone([...base.lines]);
          let run: (Json | undefined)[] = defined(structuredClone([...base.lines]));
          for (const [op, side, a, b, c] of ops)
            if (op === "blank") snapshot = snapshot.toSpliced(a % (snapshot.length + 1), 0, undefined);
            else {
              if (side !== "run") snapshot = lineMutations[op]?.(snapshot, [a, b, c]) ?? snapshot;
              if (side !== "snapshot") run = lineMutations[op]?.(run, [a, b, c]) ?? run;
            }
          const kind =
            snapshotFindingsOfBoth(snapshot, defined(run), `${base.label} ${JSON.stringify(ops)}`) === 0
              ? "none"
              : "some";
          counts.set(kind, (counts.get(kind) ?? 0) + 1);
        },
      ),
      { numRuns: runs },
    );
    t.diagnostic(`comparisons ${JSON.stringify(Object.fromEntries(counts))}`);
  });
});
