import assert from "node:assert/strict";
import { cpSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { after, test } from "node:test";
import type { TraceLine } from "../src/data/trace.generated.ts";
import { loadSpec } from "../src/load/load.ts";
import {
  decodeAnswer,
  matchRequest,
  peerSnapshots,
  readSnapshot,
  rename,
  traceName,
  verifyTraces,
} from "../src/verify/index.ts";
import { semanticsRoot } from "./examples.ts";
import { createCharge } from "./semantics/Service/Command/command-output/payments/payments.ts";
import { placeOrder } from "./semantics/Service/Command/command-output/shop/shop.ts";
import { calendar } from "./verify/mismatch/external/assumptions/calendar/contract.ts";

const commandOutput = join(semanticsRoot, "Service/Command/command-output");
const shop = await loadSpec(commandOutput);
const refund = { service: "shop", name: "refundCreatedCharge" };

mkdirSync(join(import.meta.dirname, ".fixtures"), { recursive: true });
const copies = mkdtempSync(join(import.meta.dirname, ".fixtures", "verify-api-"));
after(() => rmSync(copies, { recursive: true, force: true }));
const copyOfCommandOutput = (name: string) => {
  const copy = join(copies, name);
  cpSync(commandOutput, copy, { recursive: true });
  return copy;
};

test("readSnapshot reads snapshot lines with the trace line schema and throws when a line is unreadable", async () => {
  assert.equal(readSnapshot(shop, refund)[0]?.type, "command");
  const broken = await loadSpec(copyOfCommandOutput("unreadable"));
  writeFileSync(join(broken.root, "shop/__snapshots__/refundCreatedCharge.jsonl"), '{"type":"nothing"}\n');
  assert.throws(() => readSnapshot(broken, refund));
});

test("peerSnapshots returns the peer runs that have a snapshot, which readSnapshot reads", async () => {
  const spec = await loadSpec(join(import.meta.dirname, "verify/uncomparable/pairing/peer-runs"));
  const snapshots = peerSnapshots(spec);
  assert.deepEqual(snapshots, [{ service: "notifier", name: "announcesAdded.todo", runner: "todo" }]);
  assert.equal(readSnapshot(spec, snapshots[0] as (typeof snapshots)[number]).length, 4);
});

test("verifyTraces reports snapshot lines that do not fit the schema as violations without throwing", async () => {
  const broken = await loadSpec(copyOfCommandOutput("schema"));
  const snapshot = join(broken.root, "shop/__snapshots__/refundCreatedCharge.jsonl");
  const traces = join(copies, "schema-traces");
  mkdirSync(join(traces, "shop"), { recursive: true });
  cpSync(snapshot, join(traces, "shop/refundCreatedCharge.jsonl"));
  const text = readFileSync(snapshot, "utf8").split("\n");
  writeFileSync(snapshot, [...text.slice(0, 2), "{", ...text.slice(2)].join("\n"));
  assert.deepEqual(
    verifyTraces(broken, traces).problems.map((p) => [p.location, p.kind]),
    [[{ file: "shop/__snapshots__/refundCreatedCharge.jsonl", line: 3 }, "Uncomparable.lineSchema"]],
  );
});

test("traceName prefixes a definition name with its service name, except for definitions of the from service", () => {
  assert.equal(traceName(shop, placeOrder), "shop.placeOrder");
  assert.equal(traceName(shop, createCharge), "payments.createCharge");
  assert.equal(traceName(shop, placeOrder, "shop"), "placeOrder");
});

test("decodeAnswer decodes the output of an answer with the output schema and returns an answer without output unchanged", () => {
  const day = decodeAnswer(calendar.nextDay, { result: "fulfilled", output: { day: "2026-10-27T00:00:00Z" } });
  assert.ok(day.result === "fulfilled" && day.output.day.equals(Temporal.Instant.from("2026-10-27T00:00:00Z")));
  const unavailable = { result: "rejected", rejection: { kind: "unavailable" } } as const;
  assert.deepEqual(decodeAnswer(calendar.nextDay, unavailable), unavailable);
  const charge = decodeAnswer(createCharge, { result: "accepted", output: { chargeId: "ch_1" } });
  assert.ok(charge.result === "accepted" && charge.output.chargeId === "ch_1");
});

test("verifyTraces compares an external service trace under any name with the contract and reads Temporal values that JSON.stringify wrote", async () => {
  const spec = await loadSpec(join(import.meta.dirname, "verify/mismatch/external/assumptions"));
  const time = "2026-10-26T00:00:00Z";
  const monday = Temporal.Instant.from(time);
  const kinds = (name: string, day: Temporal.Instant) => {
    const traces = join(copies, name);
    mkdirSync(join(traces, "calendar"), { recursive: true });
    const lines = [
      { time, dir: "in", type: "query", id: "q1", name: "nextDay", input: { from: monday } },
      { time, dir: "out", type: "answer", to: "q1", answer: { result: "fulfilled", output: { day } } },
    ];
    writeFileSync(join(traces, "calendar", `${name}.jsonl`), lines.map((l) => `${JSON.stringify(l)}\n`).join(""));
    return verifyTraces(spec, traces).problems.map((p) => p.kind);
  };
  assert.deepEqual(kinds("nextDay", monday.add({ hours: 24 })), []);
  assert.deepEqual(kinds("sameDay", monday), ["Mismatch.failedAssumedEnsures"]);
});

test("matchRequest maps each created key to the implementation's value when the request equals the renamed snapshot request except for created keys, and returns undefined otherwise", () => {
  const time = "2026-10-25T01:00:00Z";
  const add = (taskId: unknown, parentId = "Task-1"): TraceLine =>
    ({ time, dir: "out", type: "command", id: "c1", name: "todo.addTask", input: { taskId, parentId } }) as TraceLine;
  const snapshot = { ...add("Task-2"), created: ["Task-2"] } as TraceLine;
  const renaming = new Map([["Task-1", "Task-2"]]);
  assert.deepEqual(matchRequest(snapshot, add("7c1e", "Task-2"), renaming), new Map([["Task-2", "7c1e"]]));
  assert.equal(matchRequest(snapshot, add("7c1e", "Task-1"), renaming), undefined);
  assert.equal(matchRequest(snapshot, add(7, "Task-2"), renaming), undefined);
  assert.equal(matchRequest(add("Task-2"), add("7c1e", "Task-2"), renaming), undefined);
});

test("rename replaces each string of a line that the renaming maps, at any depth", () => {
  const line = {
    time: "2026-10-25T01:00:00Z",
    dir: "in",
    type: "answer",
    id: "answer#3",
    to: "todo.tasks#1",
    answer: { result: "fulfilled", output: { tasks: [{ taskId: "Task-1", title: "Buy eggs" }] } },
  } as TraceLine;
  const renaming = new Map([
    ["todo.tasks#1", "s1"],
    ["Task-1", "7c1e"],
  ]);
  assert.deepEqual(rename(line, renaming), {
    ...line,
    to: "s1",
    answer: { result: "fulfilled", output: { tasks: [{ taskId: "7c1e", title: "Buy eggs" }] } },
  });
});
