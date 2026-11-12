import type {
  AnyCommand,
  AnyQuery,
  CommandAnswer,
  QueryAnswer,
  TraceLine,
  UntimedTraceLine,
} from "@natsuzora-dev/tazuna";
import type { Spec } from "@natsuzora-dev/tazuna/spec";
import { alike, decodeAnswer, readSnapshot, traceName } from "@natsuzora-dev/tazuna/verify";
import type { z } from "zod";

type SnapshotAnswer = Extract<TraceLine, { type: "answer" }>["answer"];

/** `name` is the name in the spec. */
export interface InputMessage {
  readonly id: string;
  readonly name: string;
  readonly input: unknown;
  readonly payload: unknown;
}

export interface ReplayAdapter {
  readonly start: (outputs: Outputs, time: Temporal.Instant) => Promise<void>;
  readonly now: () => Temporal.Instant;
  readonly advanceTo: (time: Temporal.Instant) => Promise<void>;
  /**
   * Resolves when the app has stopped writing outputs and `isReady` holds. `outputs` counts the trace's output lines;
   * `isReady` holds when the app has sent the request that the next answer line answers.
   */
  readonly untilQuiet: (outputs: () => number, isReady: () => boolean) => Promise<void>;
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
  readonly event: (event: { readonly name: string; readonly payload: unknown }) => void;
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
  readonly line: TraceLine;
  readonly subscription: boolean;
}

/**
 * Gives the input lines of the scenario's snapshot to the app in order, and returns the trace at the app's boundary. A
 * request that the app sent to another service waits for the snapshot's answer line, which goes to the earliest request
 * with the same name and input.
 */
export async function replay(
  spec: Spec,
  scenario: { readonly service: string; readonly name: string },
  adapter: ReplayAdapter,
): Promise<TraceLine[]> {
  const snapshot = readSnapshot(spec, scenario);
  const lines: (TraceLine | undefined)[] = [];
  const waiting = new Map<string, Waiting>();
  const appIds = new Map<string, string>();
  const subscriptions = new Map<string, AbortController>();
  let sent = 0;

  const place = () => ({ at: lines.push(undefined) - 1, time: adapter.now() });
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
    waiting.set(appId, {
      ...request,
      id: appId,
      line: asJson(lines[at.at]) as TraceLine,
      subscription: type === "subscribe",
    });
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
        write({ dir: "out", type: "unsubscribe", to: subscription }, at);
      },
      event: ({ name, payload }) => write({ dir: "out", type: "event", name, payload }, at),
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
  const writeAnswer = (to: string, answer: SnapshotAnswer) => write({ dir: "out", type: "answer", to, answer });

  function waitingRequest(to: string): Waiting | undefined {
    const request = snapshot.find((l) => l.dir === "out" && l.id === to);
    if (request?.type !== "command" && request?.type !== "query" && request?.type !== "subscribe")
      throw new Error(`the snapshot has no request ${to}`);
    return [...waiting.values()].find((w) => alike(request, w.line, request.created));
  }

  function takeAndBindWaitingRequest(to: string): Waiting {
    const found = waitingRequest(to);
    if (found === undefined) throw new Error(`no request waits for the answer to ${to}`);
    if (!found.subscription) waiting.delete(found.id);
    appIds.set(to, found.id);
    return found;
  }

  async function give(line: TraceLine): Promise<void> {
    if (line.type === "answer") {
      const request = takeAndBindWaitingRequest(line.to);
      write({ ...line, to: request.id });
      return request.answer(line.answer);
    }
    if (line.type === "event" && line.resultOf !== undefined)
      write({ ...line, resultOf: appIds.get(line.resultOf) ?? line.resultOf });
    else write(line);
    const { id } = line;
    if (id === undefined) throw new Error(`the snapshot line ${JSON.stringify(line)} has no id`);
    switch (line.type) {
      case "time":
        return;
      case "restart":
        // The requests that the old process sent get no answers.
        for (const [id, request] of waiting) if (!request.subscription) waiting.delete(id);
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
  await adapter.start(outputs, Temporal.Instant.from(first.time));
  const always = () => true;
  for (const line of snapshot) {
    if (line.dir === "out") continue;
    const time = Temporal.Instant.from(line.time);
    if (!time.equals(adapter.now())) {
      await adapter.untilQuiet(outputCount, always);
      await adapter.advanceTo(time);
    }
    const answered = line.type === "answer" ? line.to : undefined;
    await adapter.untilQuiet(
      outputCount,
      answered === undefined ? always : () => waitingRequest(answered) !== undefined,
    );
    await give(line);
  }
  await adapter.untilQuiet(outputCount, always);
  for (const controller of subscriptions.values()) controller.abort();
  await adapter.untilQuiet(outputCount, always);
  return lines.filter((l) => l !== undefined);
}

function required<F>(receive: F | undefined, type: string): F {
  if (receive === undefined) throw new Error(`the adapter receives no ${type} line`);
  return receive;
}

const asJson = (value: unknown): unknown => JSON.parse(JSON.stringify(value));
