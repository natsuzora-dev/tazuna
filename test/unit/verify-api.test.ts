import assert from "node:assert/strict";
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { join, relative } from "node:path";
import { after, test } from "node:test";
import { verifyTraces } from "../../src/cli/verify.ts";
import { type Adapter, commandRequest, decodeAnswer, drive, snapshotRuns } from "../../src/verify/index.ts";
import { checkedRoot, fixture } from "../fixtures/fixtures.ts";
import { payments } from "../fixtures/test/noViolations/command-output/payments/contract.ts";
import { createCharge } from "../fixtures/test/noViolations/command-output/payments/payments.ts";
import { calendar } from "../fixtures/verify/Mismatch/assumptions/calendar/contract.ts";

const commandOutput = fixture("test", "noViolations", "command-output");
const shop = await checkedRoot(commandOutput);
const refund = { service: "shop", scenario: "refundCreatedCharge", runner: "shop" };

mkdirSync(join(import.meta.dirname, "../.fixtures"), { recursive: true });
const copies = mkdtempSync(join(import.meta.dirname, "../.fixtures", "verify-api-"));
after(() => rmSync(copies, { recursive: true, force: true }));

test("snapshotRuns returns the own and peer runs that have a snapshot", async () => {
  const spec = await checkedRoot(fixture("verify", "Mismatch", "Mismatch.event"));
  assert.deepEqual(
    snapshotRuns(spec).filter((r) => r.runner !== r.service),
    [{ service: "notifier", scenario: "announcesAdded", runner: "todo" }],
  );
});

test("verifyTraces reports a trace line that does not fit the schema as a violation without throwing", async () => {
  const snapshot = join(shop.root, "shop/__snapshots__/refundCreatedCharge.jsonl");
  const traces = join(copies, "schema-traces");
  mkdirSync(join(traces, "shop"), { recursive: true });
  const text = readFileSync(snapshot, "utf8").split("\n");
  writeFileSync(join(traces, "shop/any-name.jsonl"), [...text.slice(0, 2), "{", ...text.slice(2)].join("\n"));
  assert.deepEqual(
    verifyTraces(shop, traces).violations.map((p) => [p.location, p.kind]),
    [[{ file: relative(shop.root, join(traces, "shop/any-name.jsonl")), line: 3 }, "Uncomparable.lineSchema"]],
  );
});

test("decodeAnswer decodes the output of an answer with the output schema and returns an answer without output unchanged", () => {
  const day = decodeAnswer(calendar.nextDay, { result: "fulfilled", output: { day: Date.UTC(2026, 9, 27) } });
  assert.ok(day.result === "fulfilled" && day.output.day === Date.UTC(2026, 9, 27));
  const unavailable = { result: "rejected", rejection: { kind: "unavailable" } } as const;
  assert.deepEqual(decodeAnswer(calendar.nextDay, unavailable), unavailable);
  const charge = decodeAnswer(createCharge, { result: "accepted", output: { chargeId: "ch_1" } });
  assert.ok(charge.result === "accepted" && charge.output.chargeId === "ch_1");
});

test("verifyTraces compares an external service trace under any name with the contract", async () => {
  const spec = await checkedRoot(fixture("verify", "Mismatch", "assumptions"));
  const time = Date.UTC(2026, 9, 26);
  const monday = time;
  const kinds = (name: string, day: number) => {
    const traces = join(copies, name);
    mkdirSync(join(traces, "calendar"), { recursive: true });
    const lines = [
      {
        time,
        dir: "in",
        type: "query",
        id: "q1",
        name: "nextDay",
        input: { from: monday },
        caller: { service: "client" },
      },
      { time, dir: "out", type: "answer", id: "answer#1", to: "q1", answer: { result: "fulfilled", output: { day } } },
    ];
    writeFileSync(join(traces, "calendar", `${name}.jsonl`), lines.map((l) => `${JSON.stringify(l)}\n`).join(""));
    return verifyTraces(spec, traces).violations.map((p) => p.kind);
  };
  assert.deepEqual(kinds("nextDay", monday + 86_400_000), []);
  assert.deepEqual(kinds("sameDay", monday), ["Mismatch.failedAssumedEnsures"]);
});

/**
 * An implementation of shop that charges through payments with its own request ids, and refunds the charge that
 * payments created, or a charge of its own when `refunds` says so. With `answersAfterCharge`, it answers placeOrder
 * only once payments answers the charge. `requestId` names the n-th request that it sends.
 */
function shopAdapter(
  refunds: (chargeId: string) => string,
  { answersAfterCharge = false, requestId = (n: number) => `pay-${n}` } = {},
): Adapter {
  let time: number;
  let chargeId = "";
  let requests = 0;
  let outputs: Parameters<Adapter["start"]>[0];
  return {
    async start(o, start) {
      outputs = o;
      time = start;
    },
    now: () => time,
    async advanceTo(to) {
      time = to;
    },
    settled: () => new Promise((resolve) => setImmediate(resolve)),
    async command({ id, name }) {
      requests += 1;
      if (name === "placeOrder") {
        outputs.event({ name: "orderPlaced", payload: { amount: 1200 }, resultOf: id });
        const charged = new Promise<void>((resolve) =>
          outputs.request({
            ...commandRequest(payments.createCharge, { amount: 1200 }, { service: "shop" }, (a) => {
              const output = decodeAnswer(payments.createCharge, a);
              if (output.result === "accepted") chargeId = output.output.chargeId;
              resolve();
            }),
            id: requestId(requests),
          }),
        );
        if (answersAfterCharge) await charged;
      } else {
        outputs.event({ name: "orderCancelled", payload: {}, resultOf: id });
        outputs.request({
          ...commandRequest(payments.refundCharge, { chargeId: refunds(chargeId) }, { service: "shop" }, () => {}),
          id: requestId(requests),
        });
      }
      return { result: "accepted" };
    },
  };
}

const verifyDriven = async (name: string, adapter: Adapter) => {
  const traces = join(copies, name);
  mkdirSync(join(traces, "shop"), { recursive: true });
  const trace = await drive(shop, refund, adapter);
  writeFileSync(join(traces, "shop/refundCreatedCharge.jsonl"), trace.map((l) => `${JSON.stringify(l)}\n`).join(""));
  return { trace, kinds: verifyTraces(shop, traces).violations.map((p) => p.kind) };
};

test("drive gives the implementation the snapshot's inputs and answers the requests it sends under its own ids", async () => {
  const { trace, kinds } = await verifyDriven(
    "driven",
    shopAdapter((chargeId) => chargeId),
  );
  assert.deepEqual(kinds, []);
  assert.deepEqual(
    trace.filter((l) => l.type === "answer" && l.dir === "in").map((l) => "to" in l && l.to),
    ["pay-1", "pay-2"],
  );
});

test("drive and verifyTraces report a request that the implementation sends with other content", async () => {
  const { kinds } = await verifyDriven(
    "refunds-other",
    shopAdapter(() => "ch_other"),
  );
  assert.deepEqual(kinds, ["Mismatch.request"]);
});

test("drive does not wait for a command's answer, so an answer that comes after a later input is a mismatch", async () => {
  const { kinds } = await verifyDriven(
    "answered-late",
    shopAdapter((chargeId) => chargeId, { answersAfterCharge: true }),
  );
  assert.ok(kinds.includes("Mismatch.missingAnswer"), kinds.join());
});

test("drive keeps both requests that the implementation sends under one id, and verifyTraces reports the duplicate id", async () => {
  const { trace, kinds } = await verifyDriven(
    "reused-id",
    shopAdapter((chargeId) => chargeId, { requestId: () => "pay-1" }),
  );
  assert.deepEqual(
    trace.filter((l) => "dir" in l && l.dir === "out" && l.type === "command").map((l) => "id" in l && l.id),
    ["pay-1", "pay-1"],
  );
  assert.deepEqual(kinds, ["Uncomparable.duplicateId"]);
});

const subscriptionAnswers = fixture("verify", "Mismatch", "subscription-answers");

/** A todo whose subscriptions end with an error at a restart, as when a server drops its connections. */
function droppingTodoAdapter(): Adapter {
  const titles: string[] = [];
  let open: { readonly push: () => void; readonly fail: () => void }[] = [];
  let time = 0;
  let outputs: Parameters<Adapter["start"]>[0] | undefined;
  return {
    async start(o, start) {
      outputs = o;
      time = start;
    },
    now: () => time,
    async advanceTo(to) {
      time = to;
    },
    settled: () => new Promise((resolve) => setImmediate(resolve)),
    async command({ id, input }) {
      const { taskId, title } = input as { readonly taskId: string; readonly title: string };
      titles.push(title);
      outputs?.event({ name: "taskAdded", payload: { id: taskId, title }, resultOf: id });
      for (const s of open) s.push();
      return { result: "accepted" };
    },
    async subscribe(_, signal) {
      const answers: unknown[] = [{ titles: [...titles] }];
      let failed = false;
      let wake = () => {};
      open.push({
        push: () => {
          answers.push({ titles: [...titles] });
          wake();
        },
        fail: () => {
          failed = true;
          wake();
        },
      });
      return (async function* () {
        while (true) {
          if (failed) throw new Error("connection reset by the restart");
          const output = answers.shift();
          if (output !== undefined) yield { result: "fulfilled" as const, output };
          else if (signal.aborted) return;
          else await new Promise<void>((resolve) => (wake = resolve));
        }
      })();
    },
    async restart() {
      for (const s of open) s.fail();
      open = [];
    },
  };
}

test("drive ends the subscriptions of the old process at a restart, so an iterable that throws then is no failure, and the same id subscribes anew", async () => {
  const spec = await checkedRoot(subscriptionAnswers);
  const traces = join(copies, "resubscribed");
  mkdirSync(join(traces, "todo"), { recursive: true });
  const run = { service: "todo", scenario: "resubscribeAfterRestart", runner: "todo" };
  const trace = await drive(spec, run, droppingTodoAdapter());
  writeFileSync(
    join(traces, "todo/resubscribeAfterRestart.jsonl"),
    trace.map((l) => `${JSON.stringify(l)}\n`).join(""),
  );
  const kinds = verifyTraces(spec, traces).violations.map((p) => p.kind);
  assert.deepEqual(kinds, []);
});
