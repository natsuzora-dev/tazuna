import type { z } from "zod";
import type { MarkOf } from "../data/bag.ts";
import type { Rejection } from "../data/trace.generated.ts";
import type { Shape } from "../data/values.ts";
import type { Contract, RecordsOf } from "../dsl/contract.ts";
import type {
  AnyCommand,
  AnyEvent,
  AnyQuery,
  AnyScreen,
  ChartSpec,
  Command,
  Control,
  Query,
} from "../dsl/definition.ts";
import type { EncodedPayload, PayloadShape } from "../dsl/event.ts";

type Encoded<S extends Shape> = z.input<z.ZodObject<{ -readonly [K in keyof S]: S[K] }>>;
type Request = AnyCommand | AnyQuery;
type InputShape<D> = D extends { readonly input: infer I extends Shape } ? I : never;
type OutputShape<D> =
  D extends Query<Shape, infer O>
    ? O
    : D extends Command<Shape, AnyEvent, string, string, infer O>
      ? [O] extends [undefined]
        ? never
        : O extends Shape
          ? O
          : never
      : never;
type InputOf<D> = Encoded<InputShape<D>>;

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

declare const observedBrand: unique symbol;
declare const createdBrand: unique symbol;
declare const rawBrand: unique symbol;

/**
 * A value of type `T` that the run observes, standing in a value position as a whole. It is no `T`: spreading it,
 * comparing it, computing with it or writing it into a string is a type error, since its value exists only when the
 * scenario runs.
 */
export type Observed<T> = symbol & { readonly [observedBrand]: T };

type Unwrapped<Z> =
  Z extends z.ZodOptional<infer I> ? Unwrapped<I> : Z extends z.ZodNullable<infer I> ? Unwrapped<I> : Z;

/**
 * The observed value of schema `Z`: an object's fields, and a sequence's elements by position, are observed values
 * too. A bag, set or sortedBy array has no positions: its elements are named by content or by the line that sent them.
 */
export type ObservedOf<Z> = Observed<z.input<Z>> &
  (Unwrapped<Z> extends z.ZodObject<infer S>
    ? ObservedFields<S>
    : Unwrapped<Z> extends z.ZodArray<infer E>
      ? [MarkOf<z.output<Unwrapped<Z>>>] extends [never]
        ? { readonly [index: number]: ObservedOf<E> }
        : unknown
      : unknown);
type ObservedFields<S> = { readonly [K in keyof S]-?: ObservedOf<S[K]> };
/** The observed value of an object of shape `S`, of each shape of a union. */
export type ObservedShape<S> = S extends Shape
  ? Observed<Encoded<S>> & (string extends keyof S ? unknown : ObservedFields<S>)
  : never;

/** A key that a running peer creates, which a running peer's message holds; see `created`. */
export type Created = { readonly [createdBrand]: true };

/** A value written as is, which no schema checks; see `raw`. */
export type Raw = { readonly [rawBrand]: true };

/** A written value of type `T`: each part is the value itself or an observed value of that type. */
export type Value<T> =
  | T
  | Observed<T>
  | (T extends readonly (infer E)[]
      ? readonly Value<E>[]
      : T extends object
        ? { readonly [K in keyof T]: Value<T[K]> }
        : never);

/** A value of type `T` in a running peer's message: a part may also be `created()`. */
export type PeerValue<T> =
  | T
  | Observed<T>
  | Created
  | (T extends readonly (infer E)[]
      ? readonly PeerValue<E>[]
      : T extends object
        ? { readonly [K in keyof T]: PeerValue<T[K]> }
        : never);

type SomeFields<T> = T extends readonly unknown[]
  ? Value<T>
  : T extends object
    ? { readonly [K in keyof T]?: SomeFields<T[K]> }
    : Value<T>;

export const lineIndex: unique symbol = Symbol("lineIndex");
export const factOf: unique symbol = Symbol("factOf");
export const observedRef: unique symbol = Symbol("observedRef");
export const createdMark: unique symbol = Symbol("created");
export const rawMark: unique symbol = Symbol("raw");
declare const messageKind: unique symbol;
declare const processing: unique symbol;
declare const sentByClient: unique symbol;

/** A placed line of When; Then and later lines name it by this handle. */
export interface Line {
  readonly [lineIndex]: number;
}

type MessageKind = "request" | "subscription" | "event" | "answer" | "end";

/** A message between participants, named by a handle: what a line caused, or a line that carried it. */
export interface Message<K extends MessageKind = MessageKind> {
  readonly [factOf]: unknown;
  readonly [messageKind]: K;
}

/** A request message: its target, and its input, observed when the scenario runs. */
export interface RequestMessage<T = Request, K extends "request" | "subscription" = "request" | "subscription">
  extends Message<K> {
  readonly target: T;
  readonly input: ObservedShape<InputShape<T>>;
}

/** A command or query that a participant sent while a line or the begin was processed. */
export type OutRequest<T = Request> = RequestMessage<T, "request">;

/** A subscription that a participant opened while a line or the begin was processed. */
export type OutSubscription<T = AnyQuery> = RequestMessage<T, "subscription">;

/** An event that a participant emitted while a line or the begin was processed. */
export interface EventMessage<Ev = AnyEvent> extends Message<"event"> {
  readonly event: Ev;
  /** The event's payload, observed when the scenario runs. */
  readonly payload: Ev extends AnyEvent ? ObservedShape<PayloadShape<Ev>> : never;
}

/** An answer that a handle names. `output` is its output, observed when the scenario runs. */
export interface AnswerRef<T = Request> extends Message<"answer"> {
  readonly output: ObservedShape<OutputShape<T>>;
}

/** The end of a subscription, which a handle names. */
export type EndRef = Message<"end">;

/** The instance of a screen that opened while a line or the begin was processed. */
export interface ScreenRef<Sc = AnyScreen> {
  readonly [factOf]: unknown;
  readonly screen: Sc;
}

/** What a line's processing, or the begin, caused, named by content; none or several matches are reported. */
export interface Caused {
  request<T extends Request>(target: T, pick?: { readonly input?: SomeFields<InputOf<T>> }): OutRequest<T>;
  subscription<Q extends AnyQuery>(query: Q, pick?: { readonly input?: SomeFields<InputOf<Q>> }): OutSubscription<Q>;
  /** The event `event`, as it travels to the service of contract `to` when given, or to its only receiver. */
  event<Ev extends AnyEvent>(
    event: Ev,
    pick?: { readonly payload?: SomeFields<EncodedPayload<Ev>>; readonly to?: Contract<unknown, unknown, "spec"> },
  ): EventMessage<Ev>;
  screen<Sc extends AnyScreen>(screen: Sc): ScreenRef<Sc>;
  /**
   * The one answer to the request of `request` that its receiver gave while this line or the begin was processed: the
   * own service's answer to a peer's request, or one answer of a subscription, named by the line that caused it.
   * `request` is the line that sent the request or delivered it.
   */
  answer<T>(request: RequestLine<T> | DeliveredRequest<T>): AnswerRef<T>;
  /** The end of the subscription `subscription` that its sender sent while this line or the begin was processed. */
  end(subscription: OutSubscription | PeerSubscribeLine): EndRef;
}

/** A line whose processing by a running service may cause messages, which `Caused` names and Then states. */
export interface ProcessingLine extends Line, Caused {
  readonly [processing]: true;
}

/** A request line of the client or a peer. `output` is the output of the first answer, observed when the scenario runs. */
export interface RequestLine<T = Request> extends Line {
  readonly target: T;
  /** Whether the line subscribes, so that it gets an answer each time the answer changes. */
  readonly subscribes: boolean;
  readonly output: ObservedShape<OutputShape<T>>;
}

/** A command or query line, which gets one answer. */
export interface SingleRequestLine<T = Request> extends RequestLine<T> {
  readonly subscribes: false;
}

/** A subscribe line, which gets an answer each time the answer changes. */
export interface SubscribeLine<T = Request> extends RequestLine<T> {
  readonly subscribes: true;
}

/** A request line of the client, whose request reaches its running receiver directly. */
export interface ClientRequestLine<T = Request> extends SingleRequestLine<T>, ProcessingLine {
  readonly [sentByClient]: true;
}

/** A subscribe line of the client. */
export interface ClientSubscribeLine<T = Request> extends SubscribeLine<T>, ProcessingLine {
  readonly [sentByClient]: true;
}

/** A peer's command or query line: the request in flight that it states. */
export interface PeerRequestLine<T = Request> extends SingleRequestLine<T>, RequestMessage<T, "request"> {}

/** A peer's subscribe line: the subscription in flight that it states. */
export interface PeerSubscribeLine<T = Request> extends SubscribeLine<T>, RequestMessage<T, "subscription"> {}

/** A peer's answer line: the answer in flight that it states. `output` is its output, observed when the scenario runs. */
export interface PeerAnswerLine<T = Request> extends Line, Message<"answer"> {
  readonly output: ObservedShape<OutputShape<T>>;
}

/** A peer's event line: the event in flight that it states, to its only receiver. */
export interface PeerEventLine extends Line, Message<"event"> {
  /** The event that the line states as it travels to the service of contract `receiver`. */
  to(receiver: Contract<unknown, unknown, "spec">): Message<"event">;
}

/** A peer's unsubscribe line: the end in flight that it states. */
export interface PeerEndLine extends Line, Message<"end"> {}

/** A line that delivered a request, which names the request and whose processing names what it caused. */
export interface DeliveredRequest<T = Request> extends ProcessingLine, Message<"request" | "subscription"> {
  readonly target: T;
  /** The output of the first answer to the delivered request, observed when the scenario runs. */
  readonly output: ObservedShape<OutputShape<T>>;
}

/** The line that delivered the message `M`: it names `M`, and its processing names what `M` caused. */
export type Delivered<M extends Message> =
  M extends RequestMessage<infer T>
    ? DeliveredRequest<T>
    : ProcessingLine & Message<M extends Message<infer K> ? K : never>;

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
  Cs[K] extends Control<infer P> ? (keyof P extends never ? [] : [payload: Value<Encoded<P>>]) : [];
type ResultOf = OutRequest | OutSubscription | RequestLine | null;

type ExternalRequests<P extends Peers> = {
  readonly [K in keyof P]: P[K] extends External<infer C> ? RequestOf<C> : never;
}[keyof P];
/** Nothing that `D` lacks, unless an external peer of `P` owns `D`: the client reaches running services only. */
type Reachable<P extends Peers, D> = D extends ExternalRequests<P> ? never : unknown;

interface Client<P extends Peers> {
  /** A command to the own service or to a running peer, the owner of the definition. */
  send<C extends AnyCommand>(
    command: C & Reachable<P, C>,
    input: Value<InputOf<C>> | Raw,
    options?: { readonly sameIdAs?: ClientRequestLine },
  ): ClientRequestLine<C>;
  call<Q extends AnyQuery>(query: Q & Reachable<P, Q>, input: Value<InputOf<Q>> | Raw): ClientRequestLine<Q>;
  subscribe<Q extends AnyQuery>(query: Q & Reachable<P, Q>, input: Value<InputOf<Q>> | Raw): ClientSubscribeLine<Q>;
  unsubscribe(subscription: ClientSubscribeLine): ProcessingLine;
  /** The client sends the request of `line` again with the same id. */
  resend<L extends ClientRequestLine | ClientSubscribeLine>(line: L): L;
}

interface User {
  operate<Cs extends Readonly<Record<string, Control>>, K extends keyof Cs & string>(
    screen: ScreenRef<{ readonly kind: "screen"; readonly controls: Cs }>,
    control: K,
    ...payload: PayloadArgs<Cs, K>
  ): ProcessingLine;
  /** The user looks at the screen instance; Then states what it offers at this point. */
  look<Sc extends AnyScreen>(screen: ScreenRef<Sc>): Look<Sc>;
}

type PeerAnswerOf<T> = PeerValue<AnswerOf<T>>;

/** What a peer sends; each line states one message in flight, which a line of the network delivers. */
interface PeerActor<C, W extends "run" | "external"> {
  answer<T extends RequestOf<C>>(
    request: RequestMessage<T> | DeliveredRequest<T>,
    answer: W extends "run" ? PeerAnswerOf<T> : Value<AnswerOf<T>>,
  ): PeerAnswerLine<T>;
  emit<Ev extends Extract<Members<C>, AnyEvent>>(
    event: Ev,
    payload: W extends "run" ? PeerValue<EncodedPayload<Ev>> : Value<EncodedPayload<Ev>>,
    options: { readonly resultOf: ResultOf },
  ): PeerEventLine;
  send<D extends AnyCommand>(
    command: D,
    input: W extends "run" ? PeerValue<InputOf<D>> : Value<InputOf<D>> | Raw,
  ): PeerRequestLine<D>;
  call<Q extends AnyQuery>(
    query: Q,
    input: W extends "run" ? PeerValue<InputOf<Q>> : Value<InputOf<Q>> | Raw,
  ): PeerRequestLine<Q>;
  subscribe<Q extends AnyQuery>(
    query: Q,
    input: W extends "run" ? PeerValue<InputOf<Q>> : Value<InputOf<Q>> | Raw,
  ): PeerSubscribeLine<Q>;
  unsubscribe(subscription: PeerSubscribeLine): PeerEndLine;
}

/** An external peer: the scenario writes what it sends, which its contract checks. */
interface ExternalPeer<C> extends PeerActor<C, "external"> {
  /** The peer never answers `request`, which it received. */
  leaveUnanswered(request: RequestMessage<RequestOf<C>> | DeliveredRequest<RequestOf<C>>): Line;
}

/** A running peer: each line states what its run sent, which must equal what the line writes. */
type RunningPeer<C> = PeerActor<C, "run">;

/** The actors of When. Each call places one line in call order and returns its handle. */
export interface When<P extends Peers> {
  /** What the begin of every running service at Given's start caused. */
  readonly begin: Caused;
  readonly client: Client<P>;
  readonly user: User;
  readonly peer: {
    readonly [K in keyof P as P[K] extends Skip ? never : K]: P[K] extends Run<infer C>
      ? RunningPeer<C>
      : P[K] extends External<infer C>
        ? ExternalPeer<C>
        : never;
  };
  readonly net: {
    /** The network delivers the message in flight to its receiver. */
    deliver<M extends Message>(message: M): Delivered<M>;
    /** The network delivers the delivered message again, with the same id. */
    redeliver<M extends Message>(message: M): Delivered<M>;
    /** The network loses the message: its receiver never gets it, and nothing tells its sender. */
    lose(message: Message): Line;
    /**
     * The network fails to deliver the request: its receiver never gets it, and its sender gets the transport's answer,
     * rejected as unavailable.
     */
    fail(request: RequestMessage): ProcessingLine;
    /** The message is undelivered at the end. */
    inFlight(message: Message): Line;
  };
  readonly clock: {
    /**
     * The clock advances to `time`, and every running service fires its deadlines due by then; in a tie of deadlines of
     * one service, the next of `order` that names one of them fires.
     */
    at(time: Instant, options?: { readonly order?: readonly DeadlineOf[] }): ProcessingLine;
  };
  readonly host: {
    /** The host restarts the own service, which reopens its screens as new instances. */
    restart(): ProcessingLine;
  };
}

/** An expectation of Then: an externally observable fact about a line. */
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
  | { readonly kind: "end"; readonly subscription: OutSubscription };

export function answered<T>(line: SingleRequestLine<T>, answer: Value<AnswerOf<T>>): Expectation;
export function answered<T>(line: SubscribeLine<T>, answers: readonly Value<AnswerOf<T>>[]): Expectation;
/**
 * Every answer that the receiver of the request of `line` gave to it: the one answer, or a subscription's answers in
 * order.
 */
export function answered(line: RequestLine, answers: unknown): Expectation {
  return { kind: "answered", line, answers: line.subscribes ? (answers as unknown[]) : [answers] };
}

/** The events, listed by a contract, that the own service emitted while `line` was processed, as a bag. */
export const emitted = (line: ProcessingLine, events: readonly Emitted[]): Expectation => ({
  kind: "emitted",
  line,
  events,
});

/** The requests that the own service sent, and the subscriptions it ended, while `line` was processed, as a bag. */
export const requested = (line: ProcessingLine, requests: readonly Sent[]): Expectation => ({
  kind: "requested",
  line,
  requests,
});

/** An event that the own service emitted, for Then's `emitted`. */
export const event = <Ev extends AnyEvent>(event: Ev, payload: Value<EncodedPayload<Ev>>): Emitted => ({
  event,
  payload,
});

/** A command or query that the own service sent, for Then's `requested`. */
export const request = <T extends Request>(target: T, input: Value<InputOf<T>>): Sent => ({
  kind: target.kind,
  target,
  input,
});

/** A subscription that the own service opened, for Then's `requested`. */
export const subscription = <Q extends AnyQuery>(query: Q, input: Value<InputOf<Q>>): Sent => ({
  kind: "subscribe",
  target: query,
  input,
});

/** The end of the subscription that the own service opened by the request `subscription`. */
export const endOf = (subscription: OutSubscription): Sent => ({ kind: "end", subscription });

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
export const created = (): Created => createdValue as unknown as Created;

/**
 * `value` written as is, where a request's input goes, which no schema checks: the receiver sees what a schema rejects,
 * as a client that sends malformed JSON does.
 */
export const raw = (value: unknown): Raw => Object.freeze({ [rawMark]: value }) as unknown as Raw;

/** The deadline `name` of state `state` of the chart instance `chart` names, which a clock line's order names. */
export interface DeadlineOf {
  readonly chart: ChartSpec;
  readonly state: string;
  readonly name: string;
}

/** The deadline `name` of state `state` of the chart `chart`'s one instance, for the order of a clock line. */
export const deadline = <C extends ChartSpec>(
  chart: C,
  state: keyof C["states"] & string,
  name: string,
): DeadlineOf => ({
  chart,
  state,
  name,
});

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
