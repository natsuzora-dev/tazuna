import type { z } from "zod";
import type { Rejection } from "../data/trace.generated.ts";
import type { Shape } from "../data/values.ts";
import type { Contract, RecordsOf } from "../dsl/contract.ts";
import type { AnyCommand, AnyEvent, AnyQuery, AnyScreen, Command, Control, Query } from "../dsl/definition.ts";
import type { EncodedPayload } from "../dsl/event.ts";

type Encoded<S extends Shape> = z.input<z.ZodObject<{ -readonly [K in keyof S]: S[K] }>>;
type Request = AnyCommand | AnyQuery;
type InputOf<D> = D extends { readonly input: infer I extends Shape } ? Encoded<I> : never;
type OutputOf<D> =
  D extends Query<Shape, infer O>
    ? Encoded<O>
    : D extends Command<Shape, AnyEvent, string, string, infer O>
      ? [O] extends [undefined]
        ? never
        : O extends Shape
          ? Encoded<O>
          : never
      : never;

/** An answer to the request `T`, in trace form. */
export type AnswerOf<T> =
  T extends Query<Shape, infer O>
    ? { readonly result: "fulfilled"; readonly output: Encoded<O> } | Rejected
    : T extends Command<Shape, AnyEvent, string, string, infer O>
      ?
          | ([O] extends [undefined]
              ? { readonly result: "accepted" }
              : O extends Shape
                ? { readonly result: "accepted"; readonly output: Encoded<O> }
                : never)
          | Rejected
      : never;
type Rejected = { readonly result: "rejected"; readonly rejection: Rejection };

type SomeFields<T> = T extends readonly unknown[]
  ? T
  : T extends object
    ? { readonly [K in keyof T]?: SomeFields<T[K]> }
    : T;

/** The index of the line that a line handle names. */
export const lineIndex: unique symbol = Symbol("lineIndex");
/** The fact that a handle names. */
export const factOf: unique symbol = Symbol("factOf");
/** The observed value that an observed placeholder stands for. */
export const observedRef: unique symbol = Symbol("observedRef");
/** Marks the `created()` placeholder. */
export const createdMark: unique symbol = Symbol("created");

/** A placed line of When; Then and later lines name it by this handle. */
export interface Line {
  readonly [lineIndex]: number;
}

/** A message in flight or delivered, named by a handle: what a line caused, or a line that carried it. */
interface MessageRef {
  readonly [factOf]: unknown;
}

/** A request that a running service sent while a line or the begin was processed. */
export interface OutRequest<T = Request> extends MessageRef {
  readonly target: T;
  /** The request's input, observed when the scenario runs. */
  readonly input: InputOf<T>;
}

/** An event that a running service emitted while a line or the begin was processed. */
export interface EventMessage<Ev = AnyEvent> extends MessageRef {
  readonly event: Ev;
  /** The event's payload, observed when the scenario runs. */
  readonly payload: Ev extends AnyEvent ? EncodedPayload<Ev> : never;
}

/** The instance of a screen that opened while a line or the begin was processed. */
export interface ScreenRef<Sc = AnyScreen> {
  readonly [factOf]: unknown;
  readonly screen: Sc;
}

/** What a line's processing, or the begin, caused, named by content; none or several matches are reported. */
export interface Caused {
  request<T extends Request>(target: T, pick?: { readonly input?: SomeFields<InputOf<T>> }): OutRequest<T>;
  event<Ev extends AnyEvent>(event: Ev, pick?: { readonly payload?: SomeFields<EncodedPayload<Ev>> }): EventMessage<Ev>;
  screen<Sc extends AnyScreen>(screen: Sc): ScreenRef<Sc>;
  /** The own service's answer to the request of the running peer's request line `request`. */
  answer(request: RequestLine): MessageRef;
}

/** A line whose processing caused facts that later lines and Then name. */
export interface CausedLine extends Line, Caused {}

/** A request line. `output` is the output of the answer, observed when the scenario runs. */
export interface RequestLine<T = Request> extends CausedLine {
  readonly target: T;
  readonly subscription: boolean;
  readonly output: OutputOf<T>;
}

/** A command or query line, which gets one answer. */
export interface SingleRequestLine<T = Request> extends RequestLine<T> {
  readonly subscription: false;
}

/** A subscribe line, which gets an answer each time the answer changes. */
export interface SubscribeLine<T = Request> extends RequestLine<T> {
  readonly subscription: true;
}

/** A peer's answer line. `output` is the output of the answer that it delivered, observed when the scenario runs. */
export interface AnswerLine<T = Request> extends CausedLine {
  readonly output: OutputOf<T>;
}

/** A look line: the screen instance that the user looked at, whose offers Then states. */
export interface Look<Sc = AnyScreen> extends Line {
  readonly looked: Sc;
}

/** An ISO datetime with seconds and an offset. */
export type Instant = `${number}-${number}-${number}T${number}:${number}:${number}${"Z" | `+${string}` | `-${string}`}`;

export interface Run<C = unknown> {
  readonly role: "run";
  readonly contract: C;
  readonly records: unknown;
}
export interface External<C = unknown> {
  readonly role: "external";
  readonly contract: C;
}
export interface Skip<C = unknown> {
  readonly role: "skip";
  readonly contract: C;
  readonly because: string;
}
export type PeerEntry = Run | External | Skip;
type Peers = Readonly<Record<string, PeerEntry>>;

/** The peer runs its spec from `records` and checks every line it takes part in. */
export const run = <C extends Contract<unknown, unknown, "spec">>(contract: C, records: RecordsOf<C>): Run<C> => ({
  role: "run",
  contract,
  records,
});

/** The peer is an external service: the scenario writes its answers and events, which its contract checks. */
export const external = <C extends Contract<unknown, unknown, "external">>(contract: C): External<C> => ({
  role: "external",
  contract,
});

/** The peer exists but does not run, and messages to it are not delivered; `because` says why. */
export const skip = <C extends Contract<unknown, unknown, "spec" | "external">>(
  contract: C,
  because: string,
): Skip<C> => ({ role: "skip", contract, because });

/** The arrangement: every running service begins at `start`, the own service from `records`. */
export interface Given<R, P extends Peers> {
  readonly start: Instant;
  readonly records: R;
  /** Every service that exchanges messages with the own service, keyed by its service name. */
  readonly peers: P;
}

type Members<C> = C[keyof C];

/** The commands and queries of contract `C`. */
export type RequestOf<C> = Extract<Members<C>, Request>;
type PayloadArgs<Cs, K extends keyof Cs> =
  Cs[K] extends Control<infer P> ? (keyof P extends never ? [] : [payload: Encoded<P>]) : [];
type ResultOf = OutRequest | RequestLine | null;

interface Client {
  /** A command to the own service or to a running peer, the owner of the definition. */
  send<C extends AnyCommand>(
    command: C,
    input: InputOf<C>,
    options?: { readonly sameIdAs?: RequestLine },
  ): SingleRequestLine<C>;
  call<Q extends AnyQuery>(query: Q, input: InputOf<Q>): SingleRequestLine<Q>;
  subscribe<Q extends AnyQuery>(query: Q, input: InputOf<Q>): SubscribeLine<Q>;
  unsubscribe(subscription: SubscribeLine): Line;
  /** The client sends the request of `line` again with the same id. */
  resend<L extends RequestLine>(line: L): L;
}

interface User {
  operate<Cs extends Readonly<Record<string, Control>>, K extends keyof Cs & string>(
    screen: ScreenRef<{ readonly kind: "screen"; readonly controls: Cs }>,
    control: K,
    ...payload: PayloadArgs<Cs, K>
  ): CausedLine;
  /** The user looks at the screen instance; Then states what it offers at this point. */
  look<Sc extends AnyScreen>(screen: ScreenRef<Sc>): Look<Sc>;
}

interface AnsweringPeer<C> {
  answer<T extends RequestOf<C>>(request: OutRequest<T>, answer: AnswerOf<T>): AnswerLine<T>;
  emit<Ev extends Extract<Members<C>, AnyEvent>>(
    event: Ev,
    payload: EncodedPayload<Ev>,
    options: { readonly resultOf: ResultOf },
  ): CausedLine;
}

interface ExternalPeer<C> extends AnsweringPeer<C> {
  /** The peer never answers `request`. */
  leaveUnanswered(request: OutRequest<RequestOf<C>>): Line;
}

/** A running peer: its lines deliver what its run sent, which must equal what the line writes. */
interface RunningPeer<C> extends AnsweringPeer<C> {
  send<D extends AnyCommand>(command: D, input: InputOf<D>): SingleRequestLine<D>;
  call<Q extends AnyQuery>(query: Q, input: InputOf<Q>): SingleRequestLine<Q>;
  subscribe<Q extends AnyQuery>(query: Q, input: InputOf<Q>): SubscribeLine<Q>;
  unsubscribe(subscription: SubscribeLine): Line;
}

type Message = Line | MessageRef;

/** The actors of When. Each call places one line in call order and returns its handle. */
export interface When<P extends Peers> {
  /** What the begin of every running service at Given's start caused. */
  readonly begin: Caused;
  readonly client: Client;
  readonly user: User;
  readonly peer: {
    readonly [K in keyof P as P[K] extends Skip ? never : K]: P[K] extends Run<infer C>
      ? RunningPeer<C>
      : P[K] extends External<infer C>
        ? ExternalPeer<C>
        : never;
  };
  readonly net: {
    deliver(message: Message): CausedLine;
    /** The network delivers the delivered message again, with the same id. */
    redeliver(message: Message): CausedLine;
    lose(message: Message): Line;
    /** The messages on the channel of `message`, either way, that are undelivered at the end are in flight. */
    inFlight(message: Message): Line;
  };
  readonly clock: {
    /** The clock advances to `time`, and every running service fires its deadlines due by then. */
    at(time: Instant): CausedLine;
  };
  readonly host: {
    /** The host restarts the own service. */
    restart(): CausedLine;
  };
}

/** An expectation of Then: an externally observable fact of the own service, about a line. */
export type Expectation =
  | { readonly kind: "answered"; readonly line: Line; readonly answers: readonly unknown[] }
  | { readonly kind: "emitted"; readonly line: Line; readonly events: readonly Emitted[] }
  | { readonly kind: "requested"; readonly line: Line; readonly requests: readonly Sent[] }
  | {
      readonly kind: "offered";
      readonly look: Line;
      readonly control: string;
      readonly payload: unknown;
      readonly offered: boolean;
    };

/** An event of Then's `emitted`. */
export interface Emitted {
  readonly event: AnyEvent;
  readonly payload: unknown;
}

/** A request of Then's `requested`, or the end of a subscription. */
export type Sent =
  | { readonly kind: "command" | "query" | "subscribe"; readonly target: Request; readonly input: unknown }
  | { readonly kind: "end"; readonly subscription: OutRequest };

export function answered<T>(line: SingleRequestLine<T>, answer: AnswerOf<T>): Expectation;
export function answered<T>(line: SubscribeLine<T>, answers: readonly AnswerOf<T>[]): Expectation;
/** Every answer that the own service gave to the request of `line`: the one answer, or a subscription's answers in order. */
export function answered(line: RequestLine, answers: unknown): Expectation {
  return { kind: "answered", line, answers: line.subscription ? (answers as unknown[]) : [answers] };
}

/** The events, listed by a contract, that the own service emitted while `line` was processed, as a bag. */
export const emitted = (line: Line, events: readonly Emitted[]): Expectation => ({ kind: "emitted", line, events });

/** The requests that the own service sent, and the subscriptions it ended, while `line` was processed, as a bag. */
export const requested = (line: Line, requests: readonly Sent[]): Expectation => ({
  kind: "requested",
  line,
  requests,
});

/** An event that the own service emitted, for Then's `emitted`. */
export const event = <Ev extends AnyEvent>(event: Ev, payload: EncodedPayload<Ev>): Emitted => ({ event, payload });

/** A command or query that the own service sent, for Then's `requested`. */
export const request = <T extends Request>(target: T, input: InputOf<T>): Sent => ({
  kind: target.kind,
  target,
  input,
});

/** A subscription that the own service opened, for Then's `requested`. */
export const subscription = <Q extends AnyQuery>(query: Q, input: InputOf<Q>): Sent => ({
  kind: "subscribe",
  target: query,
  input,
});

/** The end of the subscription that the own service opened by the request `subscription`. */
export const endOf = (subscription: OutRequest<AnyQuery>): Sent => ({ kind: "end", subscription });

/** The screen that `look` looked at offers `control` with the payload at that point. */
export const offered = <Cs extends Readonly<Record<string, Control>>, K extends keyof Cs & string>(
  look: Look<{ readonly controls: Cs }>,
  control: K,
  ...payload: PayloadArgs<Cs, K>
): Expectation => ({ kind: "offered", look, control, payload: payload[0] ?? {}, offered: true });

/** The screen that `look` looked at does not offer `control` with the payload at that point. */
export const notOffered = <Cs extends Readonly<Record<string, Control>>, K extends keyof Cs & string>(
  look: Look<{ readonly controls: Cs }>,
  control: K,
  ...payload: PayloadArgs<Cs, K>
): Expectation => ({ kind: "offered", look, control, payload: payload[0] ?? {}, offered: false });

const createdValue = Object.freeze({ [createdMark]: true });

/**
 * A key that a running peer creates, in the peer's answer, event or request: the peer's run gives the value, which the
 * scenario never writes. Later lines read it through the line's handle.
 */
export const created = (): never => createdValue as never;

/** A scenario of the own service, as the scenario file writes it. */
export interface ScenarioDefinition {
  readonly kind: "scenario";
  readonly description: string;
  readonly given: { readonly start: string; readonly records: unknown; readonly peers: Peers };
  readonly when: (w: When<Peers>) => unknown;
  /** Then, under another key, so that the definition is no thenable. */
  readonly expect: (lines: never) => readonly Expectation[];
}

/**
 * Defines a scenario of the own service: Given arranges, When places the lines in order, and Then states what the own
 * service did. The export name of the scenario is its name.
 */
export type ScenarioDefiner<R> = <const P extends Peers, N>(
  description: string,
  sections: {
    readonly given: Given<R, P>;
    readonly when: (w: When<P>) => N;
    readonly then: (lines: N) => readonly Expectation[];
  },
) => ScenarioDefinition;

export const scenarioDefiner =
  <R>(): ScenarioDefiner<R> =>
  (description, { given, when, then }) =>
    ({ kind: "scenario", description, given, when, expect: then }) as unknown as ScenarioDefinition;

export const isScenarioDefinition = (value: unknown): value is ScenarioDefinition =>
  typeof value === "object" &&
  value !== null &&
  (value as { kind?: unknown }).kind === "scenario" &&
  typeof (value as { when?: unknown }).when === "function";
