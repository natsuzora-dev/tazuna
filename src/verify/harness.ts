import { type TraceLine, traceLine } from "../data/trace.generated.ts";
import { type Bindings, substituted, type UntimedTraceLine } from "../data/trace.ts";
import { plain } from "../data/values.ts";
import type { Spec } from "../load/load.ts";
import { traceName } from "../load/traceName.ts";
import { givenRecordsOf } from "../sim/spec/simulate.ts";
import { compareTrace } from "./compare.ts";
import type { Adapter, ForeignRequest, OutputSlot, Outputs } from "./ports.ts";
import { readSnapshot } from "./snapshot.ts";

/** A run that a snapshot records: a scenario of `service`, or the run of its running peer `runner`. */
export interface Run {
  readonly service: string;
  readonly name: string;
  readonly runner?: string;
}

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

/**
 * The `in` line with the snapshot values that the bindings bind replaced in its value positions (the answered request,
 * resultOf and the content), read by the trace line schema.
 */
function substitutedLine(bindings: Bindings, line: TraceLine): TraceLine {
  const value = (v: unknown) => substituted(bindings, plain(v));
  const id = (s: string | undefined) => (s === undefined ? undefined : (bindings.get(s) ?? s));
  return traceLine.parse({
    ...line,
    ...("to" in line ? { to: id(line.to) } : {}),
    ...("resultOf" in line && line.resultOf !== undefined ? { resultOf: id(line.resultOf) } : {}),
    ...("input" in line ? { input: value(line.input) } : {}),
    ...("payload" in line ? { payload: value(line.payload) } : {}),
    ...("answer" in line ? { answer: value(line.answer) } : {}),
  });
}

/**
 * Drives the implementation through the run as the simulation ran it, and returns the trace at the implementation's
 * boundary. The implementation starts at the scenario's start from the Given records, then gets the snapshot's `in`
 * lines one by one: before each, the harness waits until the implementation has settled (Adapter.settled), and moves
 * the clock to the line's time. A command, query or subscription does not hold the harness: its answer is an output
 * that the trace gets when the implementation gives it, maybe after later inputs. A value of the snapshot that the implementation stands for in its own way (a key it created, the id of a
 * request it sent) is substituted to the implementation's value by the bindings that verify's comparison makes of the
 * trace so far, so an answer reaches the request that the implementation sent; where the binding keeps several values
 * open, it chooses by position, and the comparison reports the line as ambiguous when another choice could give the
 * implementation different inputs. Once that comparison finds the trace uncomparable, the harness gives no more lines.
 */
export async function drive(spec: Spec, run: Run, adapter: Adapter): Promise<TraceLine[]> {
  const runner = run.runner ?? run.service;
  const scenarioName = runner === run.service ? run.name : run.name.slice(0, -`.${runner}`.length);
  const scenario = spec.scenarios.find((s) => s.service === run.service && s.name === scenarioName)?.definition
    .scenario;
  if (scenario === undefined) throw new Error(`no scenario ${run.service}.${scenarioName}`);
  const snapshot = readSnapshot(spec, run);
  const lines: (TraceLine | undefined)[] = [];
  const waiting = new Map<string, Waiting>();
  const subscriptions = new Map<string, AbortController>();
  let sent = 0;
  const lineId = lineIds();

  const place = () => ({ at: lines.push(undefined) - 1, time: adapter.now() });
  const write = (line: UntimedTraceLine, { at, time } = place()) => {
    lines[at] = { ...line, time: time.toString() } as TraceLine;
  };
  const wait = (
    request: ForeignRequest,
    id: string | undefined,
    type: "command" | "query" | "subscribe",
    at: ReturnType<typeof place>,
  ): string => {
    sent += 1;
    const name = traceName(spec, request.definition);
    const appId = id ?? `${name}@${sent}`;
    write({ dir: "out", type, id: appId, name, input: plain(request.input) }, at);
    waiting.set(appId, { ...request, id: appId, subscription: type === "subscribe" });
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
        waiting.delete(subscription);
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
  const comparedBefore = (k: number) => compareTrace(spec, runner, snapshot.slice(0, k), written());

  async function give(line: TraceLine): Promise<void> {
    const { time: _, ...untimed } = line;
    write(untimed as UntimedTraceLine);
    if (line.type === "answer") {
      const request = waiting.get(line.to);
      // The settled implementation sent no request with this id, and the comparison reports the snapshot's request as
      // missing; the answer stays in the trace as its in line.
      if (request === undefined) return;
      if (!request.subscription) waiting.delete(line.to);
      return request.answer(line.answer);
    }
    const { id } = line;
    switch (line.type) {
      case "time":
        return;
      case "restart":
        // The requests that the old process sent get no answers.
        waiting.clear();
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

  await adapter.start(outputs, Temporal.Instant.from(scenario.given.start), givenRecordsOf(spec, scenario, runner));
  for (const [k, line] of snapshot.entries()) {
    if (line.dir === "out") continue;
    const time = Temporal.Instant.from(line.time);
    await adapter.settled();
    if (!time.equals(adapter.now())) {
      await adapter.advanceTo(time);
      await adapter.settled();
    }
    const compared = comparedBefore(k);
    // The comparison compares nothing after an Uncomparable finding, so the later lines would go by no binding.
    if (compared.found.some(({ kind }) => kind.startsWith("Uncomparable."))) break;
    await give(substitutedLine(compared.bindings, line));
  }
  await adapter.settled();
  for (const controller of subscriptions.values()) controller.abort();
  await adapter.settled();
  if (failures.length > 0) throw failures[0];
  return written();
}
