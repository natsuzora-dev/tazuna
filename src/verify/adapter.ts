import type { z } from "zod";
import type { CommandAnswer, QueryAnswer } from "../data/answer.ts";
import type { GivenRecord } from "../data/scenario.generated.ts";
import type { Answer } from "../data/trace.generated.ts";
import { type Shape, strictObjectOf } from "../data/values.ts";
import type { AnyCommand, AnyQuery } from "../dsl/definition.ts";

/**
 * A message that the harness gives the implementation. `name` is the name in the spec. An operation names its screen
 * instance by `nth`, its index among the open instances of the screen in opening order, only when more than one is
 * open.
 */
export interface InputMessage {
  readonly id: string;
  readonly name: string;
  readonly input: unknown;
  readonly payload: unknown;
  readonly nth?: number;
}

/**
 * What the harness controls of the implementation's world: the start from the Given records, the clock, the inputs, the
 * deliveries to the implementation and the restart. The implementation's outputs reach the harness through `Outputs`.
 */
export interface Adapter {
  /** Starts the implementation at `time` with the Given records, each value as the trace writes values. */
  readonly start: (outputs: Outputs, time: Temporal.Instant, records: readonly GivenRecord[]) => Promise<void>;
  readonly now: () => Temporal.Instant;
  /** Moves the implementation's clock to `time`, firing its timers due by then in its own order. */
  readonly advanceTo: (time: Temporal.Instant) => Promise<void>;
  /**
   * Resolves when the implementation has settled: it has no work left that it can do before it gets a message or the
   * clock moves, such as a callback or a timer due at the current time. Work that waits for an answer from another
   * service, or for a later time, does not keep it from settling. The harness relies on this alone to know that an
   * output will not come before the next input. An adapter that can only wait for the implementation to settle bounds
   * the wait and rejects with Unsettled when the bound passes.
   */
  readonly settled: () => Promise<void>;
  readonly command?: (command: InputMessage) => Promise<CommandAnswer>;
  readonly query?: (query: InputMessage) => Promise<QueryAnswer>;
  /** `signal` aborts when the subscription ends: at its unsubscribe or at a restart. */
  readonly subscribe?: (
    subscription: InputMessage,
    signal: AbortSignal,
  ) => Promise<AsyncIterable<QueryAnswer> | Iterable<QueryAnswer>>;
  readonly receive?: (event: InputMessage) => Promise<void> | void;
  readonly operate?: (operation: InputMessage) => Promise<void>;
  /** Starts a new process of the implementation on the same storage, without the timers and requests of the old one. */
  readonly restart?: () => Promise<void>;
}

/** The rejection of Adapter.settled when the implementation did not settle within `bound` milliseconds. */
export class Unsettled extends Error {
  readonly bound: number;
  constructor(bound: number) {
    super(`the implementation did not settle within ${bound} ms`);
    this.bound = bound;
  }
}

/**
 * A request that the implementation sent to another service, which the harness answers by the scenario. An answer that
 * arrives again keeps its `id`, and the implementation drops it.
 */
export interface ForeignRequest {
  readonly definition: AnyCommand | AnyQuery;
  readonly input: unknown;
  readonly answer: (answer: Answer, id: string) => void;
}

/**
 * Decodes the output of a fulfilled answer, or of an accepted answer of a command with output, with the definition's
 * output schema, and returns other answers as they are. Throws when the request has no answer with that result.
 */
export function decodeAnswer<Q extends AnyQuery>(
  query: Q,
  answer: Answer,
): QueryAnswer<z.output<z.ZodObject<Q["output"]>>>;

export function decodeAnswer<C extends AnyCommand>(
  command: C,
  answer: Answer,
): CommandAnswer<C["output"] extends Shape ? z.output<z.ZodObject<C["output"]>> : undefined>;

export function decodeAnswer(request: AnyCommand | AnyQuery, answer: Answer): Answer {
  if (answer.result === "rejected") return answer;
  if (answer.result !== (request.kind === "query" ? "fulfilled" : "accepted"))
    throw new Error(`a ${request.kind} has no ${answer.result} answer`);
  return request.output === undefined
    ? answer
    : { ...answer, output: strictObjectOf(request.output).parse(answer.output) };
}

export const commandRequest = (
  command: AnyCommand,
  input: unknown,
  answer: (answer: CommandAnswer, id: string) => void,
): ForeignRequest => ({ definition: command, input, answer: (a, id) => answer(decodeAnswer(command, a), id) });

export const queryRequest = <Q extends AnyQuery>(
  query: Q,
  input: unknown,
  answer: (answer: QueryAnswer<z.output<z.ZodObject<Q["output"]>>>, id: string) => void,
): ForeignRequest => ({ definition: query, input, answer: (a, id) => answer(decodeAnswer(query, a), id) });

/** A place in the trace where the implementation's outputs are written. */
export interface OutputSlot {
  /** `id` is the implementation's id. The harness gives one when the implementation has none. */
  readonly request: (request: ForeignRequest & { readonly id?: string }) => void;
  /** Returns the id that the harness gave the subscription. */
  readonly subscribe: (request: ForeignRequest) => string;
  readonly unsubscribe: (subscription: string) => void;
  /** `resultOf` is the id of the request whose processing emitted the event. */
  readonly event: (event: { readonly name: string; readonly payload: unknown; readonly resultOf?: string }) => void;
}

/** The end of the trace, where the implementation's outputs are written. */
export interface Outputs extends OutputSlot {
  /**
   * Reserves a slot at the current place and time, for an implementation that knows the order of its outputs before
   * their content.
   */
  readonly later: () => OutputSlot;
}
