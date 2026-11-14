import type { z } from "zod";
import type { StepName } from "../data/choiceDependent.generated.ts";
import type { Answer, DeadlineId, Rejection } from "../data/trace.generated.ts";
import type { Shape } from "../data/values.ts";
import type { AnyCommand, AnyEvent, AnyQuery, AnyScreen, Command, Control, Query } from "./definition.ts";
import type { EncodedPayload } from "./event.ts";

export type Encoded<S extends Shape> = z.input<z.ZodObject<{ -readonly [K in keyof S]: S[K] }>>;

/**
 * The fields of an input that its `in` line shows, under the line's type, with definitions in place of trace names and
 * without the fields the run derives: the generated `id`, and the `to` of an answer, which `choice` decides. `A` is the
 * answer input, which an event's `resultOf` also names.
 */
type LineFields<A> =
  | { readonly type: "command"; readonly command: AnyCommand; readonly input: unknown; readonly id?: string }
  | { readonly type: "query"; readonly query: AnyQuery; readonly input: unknown; readonly id?: string }
  | { readonly type: "subscribe"; readonly query: AnyQuery; readonly input: unknown; readonly id?: string }
  | { readonly type: "unsubscribe"; readonly to: string }
  | { readonly type: "restart" }
  | {
      readonly type: "event";
      readonly event: AnyEvent;
      readonly payload: unknown;
      readonly id?: string;
      readonly resultOf?: A;
    }
  | {
      readonly type: "operation" | "unacceptedOperation";
      readonly screen: AnyScreen;
      readonly control: string;
      readonly payload: unknown;
    }
  | A;

interface AnswerFields<C> {
  readonly type: "answer";
  readonly sender: Sender;
  readonly target: AnyCommand | AnyQuery;
  readonly answer: Answer;
  readonly choice?: C;
}

interface Timed {
  readonly time: string;
}

/**
 * The orders of an input, which only test's search sets; a scenario does not write them. `deadlineOrder` names, in
 * firing order, the deadlines that fire first in the ties during the input (InvalidInput.unreadyDeadline,
 * InvalidInput.unusedDeadlineOrder); after its entries, the first due in entry order fires. `stepOrder` names, in
 * order, the steps that the internal queue takes first during the input (InvalidInput.unreadyStep,
 * InvalidInput.unusedStepOrder).
 */
interface Scheduled {
  readonly deadlineOrder?: readonly DeadlineId[];
  readonly stepOrder?: readonly StepName[];
}

/** An input to the run: it arrives at `time`, after the deadlines due by then. */
export type Input = (LineFields<AnswerInput> | { readonly type: "time" }) & Timed & Scheduled;

type AnswerInput = AnswerFields<MockChoice | SearchChoice> & Timed;

/**
 * An answer choice whose `to` names the request by the id of its trace line. Only test's search sets it; a scenario
 * does not write it.
 */
type SearchChoice = { readonly to: string; readonly input?: never; readonly stale?: never };

/** An input as a scenario writes it, before timed() gives it the time of the `at` before it. */
type UntimedInput = LineFields<UntimedAnswer>;

type UntimedAnswer = AnswerFields<MockChoice>;

interface At extends Timed {
  readonly type: "at";
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

type ScenarioInputs = readonly [At, ...(UntimedInput | At | Elsewhere)[]];

/**
 * The options of a scenario. `given` names, by service, the start state of each spec service whose messages the
 * scenario mocks; a service it does not name starts empty.
 */
interface ScenarioOptions {
  readonly given?: Readonly<Record<string, StateInputs>>;
}

/** A scenario: the inputs given to one service, as the scenario file writes them. */
export interface Scenario {
  readonly kind: "scenario";
  readonly description: string;
  readonly inputs: ScenarioInputs;
  readonly given: Readonly<Record<string, StateInputs>>;
}

/** The options of an input. `id` is the message id, and a given id has no `#`. */
type Options<Id extends string> = { readonly id: GivenId<Id> };
type GivenId<Id extends string> = Id extends `${string}#${string}` ? never : Id;

/**
 * Defines a scenario: inputs to one service in time order, in trace form (datetime and date values as strings). The
 * export name of the scenario is its name; test compares the trace of its run with its snapshot (Mismatch.line).
 */
export function scenario(description: string, inputs: ScenarioInputs, options: ScenarioOptions = {}): Scenario {
  return { kind: "scenario", description, inputs, given: options.given ?? {} };
}

type Entry = { readonly input: UntimedInput | { readonly type: "time" }; readonly time: string };

/** Returns the entries with times; an event's `resultOf` names the answer input of the mock's first placement. */
function timedEntries(entries: readonly Entry[]): Input[] {
  const timedOf = ({ input, time }: Entry) => ({ ...input, time }) as Input;
  const answers = entries.map((e) => (e.input.type === "answer" ? (timedOf(e) as AnswerInput) : undefined));
  const first = new Map<UntimedInput, AnswerInput>();
  entries.forEach(({ input }, i) => {
    if (input.type === "answer" && !first.has(input)) first.set(input, answers[i] as AnswerInput);
  });
  return entries.map((e, i): Input => {
    const { input, time } = e;
    if (input.type !== "event" || input.resultOf === undefined) return answers[i] ?? timedOf(e);
    const resultOf = first.get(input.resultOf) ?? (timedOf({ input: input.resultOf, time }) as AnswerInput);
    return { ...timedOf(e), resultOf } as Input;
  });
}

/**
 * The written lines with times: each of the service's inputs with its position from 1, and each elsewhere input with
 * its position and the number of the service's inputs before it. Each input takes the time of the `at` before it. An
 * `at` that another `at` or the end follows, with elsewhere inputs skipped, becomes a time input.
 */
function written(inputs: ScenarioInputs | StateInputs) {
  const own: { readonly entry: Entry; readonly position: number }[] = [];
  const others: {
    readonly entry: Entry;
    readonly position: number;
    readonly service: object;
    readonly before: number;
  }[] = [];
  let at = inputs[0];
  for (const [i, w] of inputs.entries()) {
    if (w.type === "at") {
      const next = inputs.slice(i + 1).find((n) => n.type !== "elsewhere");
      if (next === undefined || next.type === "at")
        own.push({ entry: { input: { type: "time" }, time: w.time }, position: i + 1 });
      at = w;
    } else if (w.type === "elsewhere")
      others.push({
        entry: { input: w.input, time: at.time },
        position: i + 1,
        service: w.service,
        before: own.length,
      });
    else own.push({ entry: { input: w, time: at.time }, position: i + 1 });
  }
  return { own, others };
}

/**
 * Returns the inputs with times, as a run takes them: the scenario's inputs to its service, or the inputs of a state.
 * The service does not take the elsewhere inputs.
 */
export function timed(scenario: { readonly inputs: ScenarioInputs | StateInputs }): Input[] {
  return timedEntries(written(scenario.inputs).own.map((o) => o.entry));
}

/**
 * Returns, for each input that `timed` returns, its position in the scenario as written, from 1 with `at` and elsewhere
 * inputs included.
 */
export function writtenPositions(scenario: Scenario): number[] {
  return written(scenario.inputs).own.map((o) => o.position);
}

/** An elsewhere input of a scenario with its time, written position, and the number of the service's inputs before it. */
export interface ElsewhereInput {
  readonly service: object;
  readonly input: Input;
  readonly position: number;
  readonly before: number;
}

/** Returns the elsewhere inputs of the scenario in written order. */
export function elsewhereInputs(scenario: Scenario): ElsewhereInput[] {
  const { others } = written(scenario.inputs);
  const inputs = timedEntries(others.map((o) => o.entry));
  return others.map(({ service, position, before }, i) => ({ service, input: inputs[i] as Input, position, before }));
}

/**
 * Gives `input` to the spec service `service`, a contract, at this point: an input of that service that the scenario's
 * service does not see, such as a command from another caller. The scenario's service skips it; test gives it to
 * `service` in the run that it derives from the scenario to check the scenario's mocks of `service`.
 */
export function elsewhere(service: Readonly<Record<string, unknown>>, input: UntimedInput): Elsewhere {
  return { type: "elsewhere", service, input };
}

/** Sends a command to the service. */
export function send<I extends Shape, const Id extends string>(
  command: Command<I>,
  input: Encoded<I>,
  options?: Options<Id>,
): UntimedInput {
  return { type: "command", command, input, ...options };
}

/** Calls a query of the service once. */
export function call<I extends Shape, const Id extends string>(
  query: Query<I>,
  input: Encoded<I>,
  options?: Options<Id>,
): UntimedInput {
  return { type: "query", query, input, ...options };
}

type OperationArgs<Cs extends Readonly<Record<string, Control>>, K extends keyof Cs & string> = [
  target: { readonly kind: "screen"; readonly controls: Cs },
  control: K,
  ...payload: Cs[K] extends Control<infer P> ? (keyof P extends never ? [] : [Encoded<P>]) : [],
];

/** Operates a control of the screen `target` as the user. */
export function operate<Cs extends Readonly<Record<string, Control>>, const K extends keyof Cs & string>(
  ...[target, control, ...payload]: OperationArgs<Cs, K>
): UntimedInput {
  return { type: "operation", screen: target as AnyScreen, control, payload: payload[0] ?? {} };
}

/** Asserts that the screen does not accept the operation at this point. */
export function cannotOperate<Cs extends Readonly<Record<string, Control>>, const K extends keyof Cs & string>(
  ...[target, control, ...payload]: OperationArgs<Cs, K>
): UntimedInput {
  return { type: "unacceptedOperation", screen: target as AnyScreen, control, payload: payload[0] ?? {} };
}

/**
 * The choice of a mock, which answers the longest-waiting request. `input` chooses the requests that have this input,
 * and `stale` marks a late answer to a request whose state the sender left, or to an ended subscription.
 */
type MockChoice<I = unknown> = { readonly input?: I; readonly stale?: true; readonly to?: never };
type InputOfTarget<T> = T extends { readonly input: infer I extends Shape } ? Encoded<I> : never;

type Sender = { readonly kind: "screen" | "machine" | "automation" };

/** Subscribes another service to a query of the service. */
export function subscribe<I extends Shape, const Id extends string>(
  query: Query<I>,
  input: Encoded<I>,
  options?: Options<Id>,
): UntimedInput {
  return { type: "subscribe", query, input, ...options };
}

/** Ends the subscription `id` from another service. */
export function unsubscribe(id: string): UntimedInput {
  return { type: "unsubscribe", to: id };
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

/**
 * Answers, from another service, the longest-waiting request among those that a definition of kind `sender.kind` has
 * sent and the choice chooses. The target in `pair` is a query or command that the sender uses
 * (Illegal.unrequestedAnswer).
 */
export function mock<const T extends AnyCommand | AnyQuery>(
  sender: Sender,
  pair: readonly [T, MockAnswer<T>] | readonly [T, MockAnswer<T>, MockChoice<InputOfTarget<T>>],
): Mock<T> {
  const [target, answer, choice] = pair;
  return {
    type: "answer",
    sender,
    target,
    answer: answer as Answer,
    ...(choice === undefined ? {} : { choice: choice as MockChoice }),
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

/**
 * Sets the time at which the following inputs arrive: an ISO datetime with seconds, an offset, and no part below a
 * millisecond (Malformed.unparsableTime), not before the time that the inputs before it reached
 * (InvalidInput.earlierAt).
 */
export function at(time: string): At {
  return { type: "at", time };
}
