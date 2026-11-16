// Only verify's examples still write scenarios as input lists, which test does not run; verify's move to the
// simulation (P5) moves them to given/when/then and deletes this file.
import type { z } from "zod";
import type { Answer, Rejection } from "../data/trace.generated.ts";
import type { Shape } from "../data/values.ts";
import type { AnyCommand, AnyEvent, AnyQuery, AnyScreen, Command, Control, Query } from "./definition.ts";
import type { EncodedPayload } from "./event.ts";

export type Encoded<S extends Shape> = z.input<z.ZodObject<{ -readonly [K in keyof S]: S[K] }>>;

/**
 * The fields of an input that its `in` line shows, under the line's type, with definitions in place of trace names and
 * without the fields the run derives: the generated `id`, the `to` of an answer, which `choice` decides, and the `to` of
 * an unsubscribe, which `subscription` decides. `A` is the answer input, which an event's `resultOf` also names, and `U`
 * the unsubscribe input.
 */
type LineFields<A, U> =
  | CommandLine
  | QueryLine
  | SubscribeLine
  | U
  | { readonly type: "restart" }
  | ({
      readonly type: "event";
      readonly event: AnyEvent;
      readonly payload: unknown;
      readonly id?: string;
      readonly resultOf?: A;
    } & CreatesKeys)
  | ({
      readonly type: "operation";
      readonly screen: AnyScreen;
      readonly control: string;
      readonly payload: unknown;
    } & CreatesKeys)
  | {
      readonly type: "unacceptedOperation";
      readonly screen: AnyScreen;
      readonly control: string;
      readonly payload: unknown;
    }
  | A;

type CommandLine = {
  readonly type: "command";
  readonly command: AnyCommand;
  readonly input: unknown;
  readonly id?: string;
} & CreatesKeys;

type QueryLine = {
  readonly type: "query";
  readonly query: AnyQuery;
  readonly input: unknown;
  readonly id?: string;
} & CreatesKeys;

/** A subscribe input. */
type SubscribeLine = {
  readonly type: "subscribe";
  readonly query: AnyQuery;
  readonly input: unknown;
  readonly id?: string;
  readonly handle?: string;
} & CreatesKeys;

/**
 * The createKey values that the input's processing creates, by entity name, in creation order within the input: createKey
 * returns these strings in place of `<entity>-<n>` (Lean's Step.keys). A later line names a created key by its string,
 * never by `<entity>-<n>` (Illegal.countedKey).
 */
type Keys = Readonly<Record<string, readonly string[]>>;

interface CreatesKeys {
  readonly keys?: Keys;
}

interface AnswerFields<C> extends CreatesKeys {
  readonly type: "answer";
  readonly sender: Sender;
  readonly target: AnyCommand | AnyQuery;
  readonly answer: Answer;
  readonly choice?: C;
}

/** An input as a scenario writes it. */
export type UntimedInput = LineFields<UntimedAnswer, UntimedUnsubscribe>;

type UntimedUnsubscribe = { readonly type: "unsubscribe"; readonly subscription: SubscribeLine };

/** A request to the scenario's service, which `from` can say another spec service sends. */
type RequestLine = CommandLine | QueryLine | SubscribeLine | UntimedUnsubscribe;

type UntimedAnswer = AnswerFields<MockChoice>;

export interface At extends CreatesKeys {
  readonly type: "at";
  readonly time: string;
}

/**
 * A start state of a spec service, as its contract's `states` writes it: inputs to the service in time order, which a
 * scenario of another service names in `given`.
 */
export type StateInputs = readonly [At, ...(UntimedInput | At)[]];

/** An input to the spec service `service`, a contract, that the scenario's service does not take. */
interface Elsewhere {
  readonly type: "elsewhere";
  readonly service: object;
  readonly input: UntimedInput;
}

/** A request to the scenario's service that the spec service of the contract `service` sends. */
interface From {
  readonly type: "from";
  readonly service: object;
  readonly input: RequestLine;
}

export type ScenarioInputs = readonly [At, ...(UntimedInput | At | Elsewhere | From)[]];

/**
 * The options of a scenario. `given` names, by service, the start state of each spec service whose messages the
 * scenario mocks; a service it does not name starts empty.
 */
/** A scenario: the inputs given to one service, as the scenario file writes them. */
export interface Scenario {
  readonly kind: "scenario";
  readonly description: string;
  readonly inputs: ScenarioInputs;
}

/** The options of an input. `id` is the message id, and a given id has no `#`; `keys` names the created keys (Keys). */
type Options<Id extends string> = { readonly id?: GivenId<Id>; readonly keys?: Keys };
type GivenId<Id extends string> = Id extends `${string}#${string}` ? never : Id;

/**
 * Defines a scenario written as inputs to one service in time order, which only verify's examples keep: test reads its
 * name and keeps its snapshot, and runs nothing.
 */
export function scenario(description: string, inputs: ScenarioInputs): Scenario {
  return { kind: "scenario", description, inputs };
}

/**
 * Gives `input`, such as a command from another caller, to the spec service of the contract `service` at this point:
 * test gives it to that service in the run that it derives from the scenario, and the scenario's service skips it.
 */
export function elsewhere(service: Readonly<Record<string, unknown>>, input: UntimedInput): Elsewhere {
  return { type: "elsewhere", service, input };
}

/**
 * Gives the request `input` to the scenario's service as one that the spec service of the contract `service` sends:
 * test checks that the run that it derives from the scenario for that service sends such a request by then, and gives
 * that run the service's answers to it.
 */
export function from(service: Readonly<Record<string, unknown>>, input: RequestLine): From {
  return { type: "from", service, input };
}

/** Sends a command to the service. */
export function send<I extends Shape, const Id extends string>(
  command: Command<I>,
  input: Encoded<I>,
  options?: Options<Id>,
): CommandLine {
  return { type: "command", command, input, ...options };
}

/** Calls a query of the service once. */
export function call<I extends Shape, const Id extends string>(
  query: Query<I>,
  input: Encoded<I>,
  options?: Options<Id>,
): QueryLine {
  return { type: "query", query, input, ...options };
}

type OperationArgs<Cs extends Readonly<Record<string, Control>>, K extends keyof Cs & string> = [
  target: { readonly kind: "screen"; readonly controls: Cs },
  control: K,
  ...payload: Cs[K] extends Control<infer P> ? (keyof P extends never ? [] : [Encoded<P>]) : [],
];

/** Operates a control of the screen `target` as the user. `options` follow the payload of a control that has one. */
export function operate<Cs extends Readonly<Record<string, Control>>, const K extends keyof Cs & string>(
  ...args: [...OperationArgs<Cs, K>, options?: { readonly keys?: Keys }]
): UntimedInput {
  const [target, control, ...rest] = args as unknown as [AnyScreen, string, ...unknown[]];
  const hasPayload = Object.keys(target.controls?.[control]?.payload ?? {}).length > 0;
  const [payload, options] = hasPayload ? rest : [{}, ...rest];
  return { type: "operation", screen: target, control, payload: payload ?? {}, ...(options as object | undefined) };
}

/** Asserts that the screen does not accept the operation at this point. */
export function cannotOperate<Cs extends Readonly<Record<string, Control>>, const K extends keyof Cs & string>(
  ...[target, control, ...payload]: OperationArgs<Cs, K>
): UntimedInput {
  return { type: "unacceptedOperation", screen: target as AnyScreen, control, payload: payload[0] ?? {} };
}

/**
 * The choice of a mock. `input` chooses the requests whose input has each of its fields equal, at any depth, an array as
 * a whole, and `stale` marks a late answer to a request whose state the sender left, or to an ended subscription.
 */
type MockChoice<I = unknown> = { readonly input?: I; readonly stale?: true; readonly to?: never };
type InputOfTarget<T> = T extends { readonly input: infer I extends Shape } ? SomeFields<Encoded<I>> : never;
type SomeFields<T> = T extends readonly unknown[]
  ? T
  : T extends object
    ? { readonly [K in keyof T]?: SomeFields<T[K]> }
    : T;

type Sender = { readonly kind: "screen" | "machine" | "automation" };

/** Subscribes another service to a query of the service; unsubscribe takes the returned input to end it. */
export function subscribe<I extends Shape, const Id extends string>(
  query: Query<I>,
  input: Encoded<I>,
  options?: Options<Id>,
): SubscribeLine {
  return { type: "subscribe", query, input, ...options };
}

/** Ends, from another service, the subscription that the subscribe input `subscription` opened. */
export function unsubscribe(subscription: SubscribeLine): UntimedUnsubscribe {
  return { type: "unsubscribe", subscription };
}

/**
 * Restarts the service, as its environment does: the records stay, and the service begins again as at the first input.
 */
export function restart(): UntimedInput {
  return { type: "restart" };
}

type MockAnswer<T> =
  T extends Query<Shape, infer O>
    ? { result: "fulfilled"; output: Encoded<O> } | { result: "rejected"; rejection: Rejection }
    : T extends Command<Shape, AnyEvent, string, string, infer O>
      ? AcceptedAnswer<O> | { result: "rejected"; rejection: Rejection }
      : never;
type AcceptedAnswer<O> = [O] extends [undefined]
  ? { result: "accepted" }
  : O extends Shape
    ? { result: "accepted"; output: Encoded<O> }
    : never;

/** Answers, from another service, a request that a definition of kind `sender.kind` has sent. */
export function mock<const T extends AnyCommand | AnyQuery>(
  sender: Sender,
  pair: readonly [T, MockAnswer<T>] | readonly [T, MockAnswer<T>, MockChoice<InputOfTarget<T>>],
  options?: { readonly keys?: Keys },
): Mock<T> {
  const [target, answer, choice] = pair;
  return {
    type: "answer",
    sender,
    target,
    answer: answer as Answer,
    ...(choice === undefined ? {} : { choice: choice as MockChoice }),
    ...options,
  } as Mock<T>;
}

type Mock<T> = T extends { readonly kind: "command"; readonly emits: readonly (infer Ev)[] }
  ? UntimedAnswer & { readonly "~emits": (event: Ev) => void }
  : UntimedAnswer;

/**
 * The options of a received event. `resultOf` is the mock that answered the command request whose result the event is.
 * Without it, the other service emitted the event on its own.
 */
type ReceiveOptions<Ev, Id extends string> =
  | (Options<Id> & { readonly resultOf?: ResultOf<Ev> })
  | { readonly id?: GivenId<Id>; readonly resultOf: ResultOf<Ev> };
type ResultOf<Ev> = UntimedAnswer & { readonly "~emits": (event: NoInfer<Ev>) => void };

/** Delivers an event of another service to the service. */
export function receive<const Ev extends AnyEvent, const Id extends string>(
  event: Ev,
  payload: EncodedPayload<Ev>,
  options?: ReceiveOptions<Ev, Id>,
): UntimedInput {
  return { type: "event", event, payload, ...options };
}

/**
 * Passes a value through the type check unchanged. A scenario uses it to give, on purpose, an input that does not match
 * its schema, because a spec file has no type assertion (Restricted.as).
 */
export function unchecked(value: unknown): never {
  return value as never;
}

/** Sets the time at which the following inputs arrive. */
export function at(time: string, options?: { readonly keys?: Keys }): At {
  return { type: "at", time, ...options };
}
