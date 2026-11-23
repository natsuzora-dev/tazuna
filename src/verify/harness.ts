import type { CheckedSpec } from "../check/spec.ts";
import { ask } from "../cli/engine.ts";
import type { ReadLine } from "../cli/protocol.generated.ts";
import { InternalError } from "../data/internalError.ts";
import type { GivenRecord } from "../data/scenario.generated.ts";
import { type TraceLine, traceLine } from "../data/trace.generated.ts";
import type { Bindings, UntimedTraceLine } from "../data/trace.ts";
import type { Run } from "../data/traceFile.ts";
import { plain } from "../data/values.ts";
import { traceName } from "../load/traceName.ts";
import type { Adapter, ForeignRequest, OutputSlot, Outputs } from "./adapter.ts";
import { readSnapshot } from "./snapshot.ts";

interface Waiting extends ForeignRequest {
  readonly id: string;
  readonly subscription: boolean;
}

/** Returns a function that gives an output line without an implementation id the id `<name>#<n>`, per name. */
export function lineIds(): (name: string) => string {
  const counts = new Map<string, number>();
  return (name) => {
    const n = (counts.get(name) ?? 0) + 1;
    counts.set(name, n);
    return `${name}#${n}`;
  };
}

function required<F>(receive: F | undefined, type: string): F {
  if (receive === undefined) throw new Error(`the adapter receives no ${type} line`);
  return receive;
}

/** A value as verify reads it, tagged by its variant (Lean's CValue.tagged). */
type Tagged =
  | { readonly leaf: unknown }
  | { readonly ref: readonly [string, string] }
  | { readonly arr: readonly Tagged[] }
  | { readonly bag: readonly Tagged[] }
  | { readonly runs: readonly Tagged[] }
  | { readonly obj: readonly (readonly [string, Tagged])[] };

/** Returns `value` as plain JSON, with each key reference that `bindings` binds replaced by its bound value. */
function substitutedRefs(bindings: Bindings, value: Tagged): unknown {
  if ("leaf" in value) return value.leaf;
  if ("ref" in value) return bindings.get(value.ref[1]) ?? value.ref[1];
  if ("arr" in value) return value.arr.map((v) => substitutedRefs(bindings, v));
  if ("bag" in value) return value.bag.map((v) => substitutedRefs(bindings, v));
  if ("runs" in value) return value.runs.flatMap((r) => substitutedRefs(bindings, r) as unknown[]);
  return Object.fromEntries(value.obj.map(([k, v]) => [k, substitutedRefs(bindings, v)]));
}

/**
 * The `in` line as verify reads it, with the snapshot values that the bindings bind replaced in its key positions:
 * the answered request, resultOf and the key references of the content. Any other string stays as the snapshot has it.
 */
function substitutedLine(bindings: Bindings, read: ReadLine): TraceLine {
  const { line } = read;
  const value = read.value === undefined ? undefined : plain(substitutedRefs(bindings, read.value as Tagged));
  const id = (s: string | undefined) => (s === undefined ? undefined : (bindings.get(s) ?? s));
  const content =
    value === undefined
      ? {}
      : line.type === "command" || line.type === "query" || line.type === "subscribe"
        ? { input: value }
        : line.type === "event" || line.type === "operation"
          ? { payload: value }
          : line.type === "answer" && "output" in line.answer
            ? { answer: { ...line.answer, output: value } }
            : {};
  return traceLine.parse({
    ...line,
    ...("to" in line ? { to: id(line.to) } : {}),
    ...("resultOf" in line && line.resultOf !== undefined ? { resultOf: id(line.resultOf) } : {}),
    ...content,
  });
}

/** The first line of a log: the time and the records that the implementation starts from. */
interface StartLine {
  readonly type: "start";
  readonly time: number;
  readonly records: readonly GivenRecord[];
}

/** A line of a log that verify reads: its start line, then trace lines. */
export type LogLine = StartLine | TraceLine;

/**
 * Drives the implementation through the run as the simulation ran it, and returns the log at the implementation's
 * boundary: its start line, then its trace. The implementation starts at the scenario's start from the Given records,
 * then gets the snapshot's `in` lines one by one: before each, the harness waits until the implementation has settled
 * (Adapter.settled), and moves the clock to the line's time. A command, query or subscription does not hold the
 * harness: its answer is an output that the log gets when the implementation gives it, maybe after later inputs. A
 * value of the snapshot that the implementation stands for in its own way (a key it created, the id of a request it
 * sent) is substituted to the implementation's value by the first of the bindings under which the log so far compares
 * with the snapshot so far, so an answer reaches the request that the implementation sent. Once that comparison finds
 * the log uncomparable, the harness gives no more lines. Comparing reads values by their schemas alone, so drive runs
 * no spec function, and verify's replay of the log is what checks it.
 */
export async function drive(spec: CheckedSpec, run: Run, adapter: Adapter): Promise<LogLine[]> {
  const { runner } = run;
  const scenario = spec.scenarios.find((s) => s.service === run.service && s.name === run.scenario)?.definition
    .scenario;
  if (scenario === undefined) throw new InternalError(`no scenario ${run.service}.${run.scenario}`);
  const snapshot = readSnapshot(spec, run);
  const [read] = ask("readLines", [{ structure: spec.structure, service: runner, lines: snapshot }]);
  const readSnapshotLines = read?.lines ?? [];
  const lines: (TraceLine | undefined)[] = [];
  // Keyed by who gave the id, the implementation or the harness, so that neither id hides the other.
  const waiting = new Map<string, Waiting>();
  const waitingKey = (by: "implementation" | "harness", id: string) => `${by}\u0000${id}`;
  const subscriptions = new Map<string, AbortController>();
  let sent = 0;
  const lineId = lineIds();

  const place = () => ({ at: lines.push(undefined) - 1, time: adapter.now() });
  const write = (line: UntimedTraceLine, { at, time } = place()) => {
    lines[at] = { ...line, time } as TraceLine;
  };
  const wait = (
    request: ForeignRequest,
    id: string | undefined,
    type: "command" | "query" | "subscribe",
    at: ReturnType<typeof place>,
  ): string => {
    const name = traceName(spec, request.definition);
    const requestIds = new Set(
      written().flatMap((l) => (l.type === "command" || l.type === "query" || l.type === "subscribe" ? [l.id] : [])),
    );
    do sent += 1;
    while (id === undefined && requestIds.has(`${name}@${sent}`));
    const appId = id ?? `${name}@${sent}`;
    write({ dir: "out", type, id: appId, name, input: plain(request.input) }, at);
    // A second request with the same id stays in the trace, where verify takes it as the first sent again, or reports
    // Uncomparable.duplicateId when its type, name or input differs.
    const key = waitingKey(id === undefined ? "harness" : "implementation", appId);
    if (!waiting.has(key)) waiting.set(key, { ...request, id: appId, subscription: type === "subscribe" });
    return appId;
  };
  const later = (): OutputSlot => {
    const at = place();
    return {
      request: ({ id, ...request }) => {
        wait(request, id, request.definition.kind, at);
      },
      subscribe: (request) => wait(request, undefined, "subscribe", at),
      unsubscribe: (subscription) => {
        waiting.delete(waitingKey("harness", subscription));
        write({ dir: "out", type: "unsubscribe", id: lineId("unsubscribe"), to: subscription }, at);
      },
      event: ({ name, payload, resultOf }) =>
        write(
          {
            dir: "out",
            type: "event",
            id: lineId(name),
            name,
            payload: plain(payload),
            ...(resultOf === undefined ? {} : { resultOf }),
          },
          at,
        ),
    };
  };
  const outputs: Outputs = {
    request: (request) => later().request(request),
    subscribe: (request) => later().subscribe(request),
    unsubscribe: (subscription) => later().unsubscribe(subscription),
    event: (event) => later().event(event),
    later,
  };
  const written = () => lines.filter((l) => l !== undefined);
  const failures: unknown[] = [];
  const running = (work: Promise<void>) => void work.catch((error: unknown) => failures.push(error));
  const writeAnswer = (to: string, answer: unknown) =>
    write({ dir: "out", type: "answer", id: lineId("answer"), to, answer: plain(answer) } as UntimedTraceLine);
  const [given] = ask("givenRecords", [{ structure: spec.structure, scenario, service: runner }]);
  const start: StartLine = { type: "start", time: scenario.given.start, records: given?.records ?? [] };
  const comparedBefore = (k: number) => {
    const [compared] = ask("bindings", [
      { structure: spec.structure, service: runner, snapshot: snapshot.slice(0, k), trace: written() },
    ]);
    const [first] = compared?.bindings ?? [];
    return { found: compared?.findings ?? [], first: new Map(Object.entries(first ?? {})) };
  };

  async function give(line: TraceLine): Promise<void> {
    const { time: _, ...untimed } = line;
    write(untimed as UntimedTraceLine);
    if (line.type === "answer") {
      const keys = [waitingKey("implementation", line.to), waitingKey("harness", line.to)].filter((k) =>
        waiting.has(k),
      );
      const [key] = keys;
      const request = key === undefined ? undefined : waiting.get(key);
      // With no request, the settled implementation sent none with this id, and the comparison reports the snapshot's
      // request as missing; with two, verify reports the trace's duplicateId. The answer stays in the trace as its in
      // line.
      if (key === undefined || request === undefined || keys.length > 1) return;
      if (!request.subscription) waiting.delete(key);
      return request.answer(line.answer, line.id);
    }
    const { id } = line;
    switch (line.type) {
      case "time":
        return;
      case "restart":
        // The requests that the old process sent get no answers, and its subscriptions end.
        waiting.clear();
        for (const controller of subscriptions.values()) controller.abort();
        subscriptions.clear();
        return required(adapter.restart, line.type)();
      case "command": {
        const command = required(adapter.command, line.type);
        return running((async () => writeAnswer(id, await command({ ...line, payload: undefined })))());
      }
      case "query": {
        const query = required(adapter.query, line.type);
        return running((async () => writeAnswer(id, await query({ ...line, payload: undefined })))());
      }
      case "subscribe": {
        const subscribe = required(adapter.subscribe, line.type);
        const controller = new AbortController();
        subscriptions.set(id, controller);
        return running(
          (async () => {
            try {
              for await (const answer of await subscribe({ ...line, payload: undefined }, controller.signal))
                writeAnswer(id, answer);
            } catch (error) {
              if (!controller.signal.aborted) throw error;
            }
          })(),
        );
      }
      case "unsubscribe":
        subscriptions.get(line.to)?.abort();
        return;
      case "event":
        return required(adapter.receive, line.type)({ ...line, input: undefined });
      case "operation":
        return required(adapter.operate, line.type)({ ...line, input: undefined, payload: line.payload });
    }
  }

  await adapter.start(outputs, start.time, start.records);
  for (const [k, line] of snapshot.entries()) {
    if (line.dir === "out") continue;
    await adapter.settled();
    if (line.time !== adapter.now()) {
      await adapter.advanceTo(line.time);
      await adapter.settled();
    }
    const compared = comparedBefore(k);
    // The comparison compares nothing after an Uncomparable finding, so the later lines would go by no binding.
    if (compared.found.some(({ kind }) => kind.startsWith("Uncomparable."))) break;
    const readLine = readSnapshotLines[k];
    await give(readLine === undefined || readLine === null ? line : substitutedLine(compared.first, readLine));
  }
  await adapter.settled();
  for (const controller of subscriptions.values()) controller.abort();
  await adapter.settled();
  if (failures.length > 0) throw failures[0];
  return [start, ...written()];
}
