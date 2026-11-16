import type {
  AnyCommand,
  AnyQuery,
  CommandAnswer,
  QueryAnswer,
  TraceLine,
  UntimedTraceLine,
} from "@natsuzora-dev/tazuna";
import type { Spec } from "@natsuzora-dev/tazuna/spec";
import {
  decodeAnswer,
  type GivenRecord,
  givenRecords,
  matchRequest,
  readSnapshot,
  rename,
  traceName,
} from "@natsuzora-dev/tazuna/verify";
import type { z } from "zod";
import { lineIds } from "./traces.ts";

type SnapshotAnswer = Extract<TraceLine, { type: "answer" }>["answer"];

/** `name` is the name in the spec. */
export interface InputMessage {
  readonly id: string;
  readonly name: string;
  readonly input: unknown;
  readonly payload: unknown;
}

export interface ReplayAdapter {
  /** Starts the app at `time` with the Given records of the run. */
  readonly start: (outputs: Outputs, time: Temporal.Instant, records: readonly GivenRecord[]) => Promise<void>;
  readonly now: () => Temporal.Instant;
  readonly advanceTo: (time: Temporal.Instant) => Promise<void>;
  /** Resolves when the app has stopped writing outputs. `outputs` counts the trace's output lines. */
  readonly untilQuiet: (outputs: () => number) => Promise<void>;
  readonly command?: (command: InputMessage) => Promise<CommandAnswer>;
  readonly query?: (query: InputMessage) => Promise<QueryAnswer>;
  /** `signal` aborts when the subscription ends. */
  readonly subscribe?: (
    subscription: InputMessage,
    signal: AbortSignal,
  ) => Promise<AsyncIterable<QueryAnswer> | Iterable<QueryAnswer>>;
  readonly receive?: (event: InputMessage) => Promise<void> | void;
  readonly operate?: (operation: InputMessage) => Promise<void>;
  /** Fails unless the app does not accept the operation: its control is missing or disabled. */
  readonly cannotOperate?: (operation: InputMessage) => Promise<void>;
  /** Starts a new process of the app on the same database, without the timers and requests of the old one. */
  readonly restart?: () => Promise<void>;
}

/** A request that the app sent to another service. */
export interface ForeignRequest {
  readonly definition: AnyCommand | AnyQuery;
  readonly input: unknown;
  readonly answer: (answer: SnapshotAnswer) => void;
}

export const commandRequest = (
  command: AnyCommand,
  input: unknown,
  answer: (answer: CommandAnswer) => void,
): ForeignRequest => ({ definition: command, input, answer: (a) => answer(decodeAnswer(command, a)) });

export const queryRequest = <Q extends AnyQuery>(
  query: Q,
  input: unknown,
  answer: (answer: QueryAnswer<z.output<z.ZodObject<Q["output"]>>>) => void,
): ForeignRequest => ({ definition: query, input, answer: (a) => answer(decodeAnswer(query, a)) });

/** A place in the trace where the app's outputs are written. */
export interface OutputSlot {
  /** `id` is the app's id; replay gives one when the app has none. */
  readonly request: (request: ForeignRequest & { readonly id?: string }) => void;
  /** Returns the id that replay gave the subscription. */
  readonly subscribe: (request: ForeignRequest) => string;
  readonly unsubscribe: (subscription: string) => void;
  /** `resultOf` is the id of the request whose processing emitted the event. */
  readonly event: (event: { readonly name: string; readonly payload: unknown; readonly resultOf?: string }) => void;
}

/** The end of the trace, where the app's outputs are written. */
export interface Outputs extends OutputSlot {
  /**
   * Reserves a slot at the current place and time, for an app that knows the order of its outputs before their content.
   */
  readonly later: () => OutputSlot;
}

interface Waiting extends ForeignRequest {
  readonly id: string;
  readonly subscription: boolean;
}

/**
 * Gives the input lines of the scenario's snapshot to the app in order, and returns the trace at the app's boundary. A
 * request that the app sends to another service pairs with the earliest unpaired snapshot request that `matchRequest`
 * matches and that lies between the same two input lines as the app's request, and receives that snapshot request's
 * answer lines. Replay writes an answer line to the trace without giving it to the app when no waiting app request is
 * paired with the line's snapshot request.
 */
export async function replay(
  spec: Spec,
  scenario: { readonly service: string; readonly name: string; readonly runner?: string },
  adapter: ReplayAdapter,
): Promise<TraceLine[]> {
  const snapshot = readSnapshot(spec, scenario);
  const lines: (TraceLine | undefined)[] = [];
  const unpaired: { line: TraceLine; inputsBefore: number }[] = [];
  let inputs = 0;
  for (const line of snapshot) {
    if (line.dir === "in") inputs += 1;
    else if (line.type === "command" || line.type === "query" || line.type === "subscribe")
      unpaired.push({ line, inputsBefore: inputs });
  }
  let inputsGiven = 0;
  const waiting = new Map<string, Waiting>();
  /** Maps the snapshot's request ids and created keys to the app's. */
  const renaming = new Map<string, string>();
  const subscriptions = new Map<string, AbortController>();
  let sent = 0;
  const lineId = lineIds();

  const place = () => ({ at: lines.push(undefined) - 1, time: adapter.now(), inputsBefore: inputsGiven });
  const write = (line: UntimedTraceLine, { at, time } = place()) => {
    lines[at] = { ...line, time: time.toString() };
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
    const line = { dir: "out", type, id: appId, name, input: request.input } as const;
    write(line, at);
    waiting.set(appId, { ...request, id: appId, subscription: type === "subscribe" });
    pair(asJson(lines[at.at]) as TraceLine, at.inputsBefore);
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
            payload,
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
  const outputCount = () => lines.filter((l) => l?.dir === "out").length;
  const writeAnswer = (to: string, answer: SnapshotAnswer) =>
    write({ dir: "out", type: "answer", id: lineId("answer"), to, answer });

  function pair(request: TraceLine, inputsBeforeRequest: number): void {
    for (const [i, { line: snapshotRequest, inputsBefore }] of unpaired.entries()) {
      if (inputsBefore !== inputsBeforeRequest) continue;
      const keys = matchRequest(snapshotRequest, request, renaming);
      if (keys === undefined) continue;
      unpaired.splice(i, 1);
      renaming.set(snapshotRequest.id, request.id);
      for (const [key, appKey] of keys) renaming.set(key, appKey);
      return;
    }
  }

  const isWaiting = (snapshotRequestId: string) => waiting.has(renaming.get(snapshotRequestId) ?? "");

  async function give(snapshotLine: TraceLine): Promise<void> {
    inputsGiven += 1;
    const line = rename(snapshotLine, renaming);
    write(line);
    if (line.type === "answer") {
      const request = waiting.get(line.to);
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
      case "command":
        return writeAnswer(id, await required(adapter.command, line.type)({ ...line, id, payload: undefined }));
      case "query":
        return writeAnswer(id, await required(adapter.query, line.type)({ ...line, id, payload: undefined }));
      case "subscribe": {
        const controller = new AbortController();
        subscriptions.set(id, controller);
        const message = { ...line, id, payload: undefined };
        const answers = await required(adapter.subscribe, line.type)(message, controller.signal);
        void (async () => {
          try {
            for await (const answer of answers) writeAnswer(id, answer);
          } catch (error) {
            if (!controller.signal.aborted) throw error;
          }
        })();
        return;
      }
      case "unsubscribe":
        subscriptions.get(line.to)?.abort();
        return;
      case "event":
        return required(adapter.receive, line.type)({ ...line, id, input: undefined });
      case "operation":
        return required(adapter.operate, line.type)({ ...line, id, input: undefined, payload: line.payload });
      case "unacceptedOperation":
        return required(adapter.cannotOperate, line.type)({ ...line, id, input: undefined, payload: line.payload });
    }
  }

  const [first] = snapshot;
  if (first === undefined) throw new Error(`the snapshot of ${scenario.service}/${scenario.name} has no lines`);
  await adapter.start(outputs, Temporal.Instant.from(first.time), givenRecords(spec, scenario));
  for (const line of snapshot) {
    if (line.dir === "out") continue;
    const time = Temporal.Instant.from(line.time);
    if (!time.equals(adapter.now())) {
      await adapter.untilQuiet(outputCount);
      await adapter.advanceTo(time);
    }
    await adapter.untilQuiet(outputCount);
    if (line.type === "answer")
      for (let i = 0; i < quietPeriodsBeforeAnswer && !isWaiting(line.to); i += 1)
        await adapter.untilQuiet(outputCount);
    await give(line);
  }
  await adapter.untilQuiet(outputCount);
  for (const controller of subscriptions.values()) controller.abort();
  await adapter.untilQuiet(outputCount);
  return lines.filter((l) => l !== undefined);
}

/** How many quiet periods replay waits before an answer line for the app to send the paired request, which a browser may send late. */
const quietPeriodsBeforeAnswer = 20;

function required<F>(receive: F | undefined, type: string): F {
  if (receive === undefined) throw new Error(`the adapter receives no ${type} line`);
  return receive;
}

const asJson = (value: unknown): unknown => JSON.parse(JSON.stringify(value));
