import { invalidInputKinds } from "../data/invalidInput.generated.ts";
import type { Answer, DeadlineId } from "../data/trace.generated.ts";
import { canonicalJson, type Shape } from "../data/values.ts";
import type { AnyCommand, AnyEvent, AnyQuery, ChartSpec } from "../dsl/definition.ts";
import type { Input } from "../dsl/scenario.ts";
import type { Spec } from "../load/load.ts";
import { refOfDefinition, traceName } from "../load/traceName.ts";
import type { Run } from "../run/execute.ts";
import { contractsListing, rejectionKinds } from "../syntax/structure.ts";
import { stringsIn, valuesFor } from "./values.ts";

/** The number of values tried for each payload, input, and answer. */
export const valuesPerPayload = 2;

/** The values the scenarios of a spec already use, tried first. */
export interface SeenValues {
  readonly words: readonly string[];
  readonly answers: ReadonlyMap<unknown, readonly Answer[]>;
  /** The inputs and payloads that scenarios send, call, subscribe, and receive, per command, query, and event. */
  readonly messages: ReadonlyMap<unknown, readonly unknown[]>;
  readonly payloads: ReadonlyMap<string, readonly unknown[]>;
}

export function seenValues(spec: Spec): SeenValues {
  const words = new Set<string>();
  const answers = new Map<unknown, Answer[]>();
  const messages = new Map<unknown, unknown[]>();
  const payloads = new Map<string, unknown[]>();
  const add = <K, V>(map: Map<K, V[]>, key: K, value: V) => map.set(key, [...(map.get(key) ?? []), value]);
  for (const s of spec.scenarios)
    for (const input of s.definition.inputs) {
      switch (input.type) {
        case "answer":
          add(answers, input.target, input.answer);
          break;
        case "operation":
          add(
            payloads,
            `${spec.names.get(input.screen)?.service}.${spec.names.get(input.screen)?.name}.${input.control}`,
            input.payload,
          );
          break;
        case "command":
          add(messages, input.command, input.input);
          break;
        case "query":
        case "subscribe":
          add(messages, input.query, input.input);
          break;
        case "event":
          add(messages, input.event, input.payload);
          break;
      }
      const value = "input" in input ? input.input : "payload" in input ? input.payload : undefined;
      for (const w of stringsIn(value)) words.add(w);
    }
  return { words: [...words], answers, messages, payloads };
}

function moveKey(spec: Spec, input: Input): string {
  const name = (d: unknown) => `${spec.names.get(d)?.service}.${spec.names.get(d)?.name}`;
  const order = [input.deadlineOrder ?? [], input.stepOrder ?? []];
  switch (input.type) {
    case "answer":
      return JSON.stringify([
        "answer",
        input.time,
        name(input.sender),
        name(input.target),
        input.answer,
        input.choice ?? null,
        order,
      ]);
    case "operation":
    case "unacceptedOperation":
      return JSON.stringify([input.type, input.time, name(input.screen), input.control, input.payload, order]);
    case "time":
    case "restart":
      return JSON.stringify([input.type, input.time, order]);
    case "command":
      return JSON.stringify(["command", input.time, name(input.command), input.input, order]);
    case "query":
    case "subscribe":
      return JSON.stringify([input.type, input.time, name(input.query), input.input, order]);
    case "event":
      return JSON.stringify(["event", input.time, name(input.event), input.payload, order]);
    case "unsubscribe":
      return JSON.stringify(["unsubscribe", input.time, "to" in input ? input.to : input.subscription, order]);
    case "answerTo":
      return JSON.stringify(["answerTo", input.time, input.to, name(input.target), input.answer, order]);
  }
}

const reject: Answer = { result: "rejected", rejection: { kind: "unavailable" } };

/**
 * Returns a function that lists the inputs enabled after a run, at the run's time: answers to awaited requests,
 * operations, the end of each open subscription, messages from other services, and a restart; and time inputs around
 * the next deadline. A message from another service sends a command, or calls or subscribes to a query, that the
 * service owns, or delivers an event of another service's contract.
 */
export function enabledMoves(
  spec: Spec,
  service: string,
  seen: SeenValues,
  valuesPerInput: number,
): (run: Run) => Input[] {
  const values = (d: unknown, shape: Shape) => valuesFor(shape, seen.messages.get(d) ?? [], seen.words, valuesPerInput);
  const messages = spec.definitions.flatMap(({ service: owner, definition: d }): ((time: string) => Input)[] => {
    if (d.kind === "command" && owner === service)
      return values(d, (d as AnyCommand).input).map((input) => (time) => ({
        type: "command",
        command: d as AnyCommand,
        input,
        time,
      }));
    if (d.kind === "query" && owner === service)
      return values(d, (d as AnyQuery).input).flatMap((input): ((time: string) => Input)[] => [
        (time) => ({ type: "query", query: d as AnyQuery, input, time }),
        (time) => ({ type: "subscribe", query: d as AnyQuery, input, time }),
      ]);
    if (d.kind === "event" && contractsListing(spec.structure, refOfDefinition(spec, d)).some((s) => s !== service))
      return values(d, (d as AnyEvent).payload).map((payload) => (time) => ({
        type: "event",
        event: d as AnyEvent,
        payload,
        time,
      }));
    return [];
  });
  const definition = (name: string, kinds: readonly string[]) =>
    spec.definitions.find((d) => kinds.includes(d.definition.kind) && traceName(spec, d.definition, service) === name)
      ?.definition;
  return (run) => {
    const { enabled } = run;
    if (enabled === undefined) return [];
    const now = run.now;
    const time = now.toString();
    // An ended subscription stays awaiting, but an answer to it answers no request (verify reports that), so do not
    // answer it.
    const ended = new Set(
      run.outcome.lines.flatMap((l) => (l.dir === "out" && l.type === "unsubscribe" ? [l.to] : [])),
    );
    const answers = enabled.awaiting.flatMap((a) => {
      if (ended.has(a.id)) return [];
      const sender = definition(a.sender, ["screen", "machine", "automation"]);
      const target = spec.definitions.find(
        (d) =>
          d.service === a.target &&
          d.name === a.name &&
          (d.definition.kind === "command" || d.definition.kind === "query"),
      )?.definition as AnyCommand | AnyQuery | undefined;
      if (sender === undefined || target === undefined) return [];
      const output = target.output as Shape | undefined;
      const generated = (output === undefined ? [{}] : valuesFor(output, [], seen.words, valuesPerInput)).map(
        (o): Answer =>
          target.kind === "query"
            ? { result: "fulfilled", output: o }
            : output === undefined
              ? { result: "accepted" }
              : { result: "accepted", output: o },
      );
      const listed = seen.answers.get(target) ?? [];
      const kinds = rejectionKinds(spec.structure, service, { service: a.target, name: a.name });
      const rejections = kinds.includes("unavailable") ? [reject] : [];
      const pool = new Map<string, Answer>();
      for (const answer of [listed[0] ?? generated[0], ...rejections, ...listed, ...generated])
        if (answer !== undefined) pool.set(canonicalJson(answer), answer);
      return [...pool.values()]
        .slice(0, valuesPerInput)
        .map(
          (answer): Input => ({ type: "answer", sender: sender as never, target, answer, choice: { to: a.id }, time }),
        );
    });
    const times =
      enabled.nextDeadline === undefined
        ? []
        : [
            Temporal.Instant.from(enabled.nextDeadline).subtract({ milliseconds: 1 }),
            Temporal.Instant.from(enabled.nextDeadline),
          ]
            .filter((t) => Temporal.Instant.compare(t, now) >= 0)
            .map((t): Input => ({ type: "time", time: t.toString() }));
    const operations = enabled.operations.flatMap((o) => {
      const screen = definition(o.screen, ["screen"]);
      if (screen === undefined) return [];
      const shape = ((screen as unknown as ChartSpec).controls?.[o.control]?.payload ?? {}) as Shape;
      const listed =
        seen.payloads.get(`${spec.names.get(screen)?.service}.${spec.names.get(screen)?.name}.${o.control}`) ?? [];
      const payloads =
        o.payloads === "any"
          ? valuesFor(shape, listed, seen.words, valuesPerInput)
          : o.payloads.slice(0, valuesPerInput);
      return payloads.map(
        (payload): Input => ({ type: "operation", screen: screen as never, control: o.control, payload, time }),
      );
    });
    const unsubscribes = run.openSubscriptions.map((id): Input => ({ type: "unsubscribe", to: id, time }));
    return [
      ...answers,
      ...times,
      ...operations,
      ...unsubscribes,
      ...messages.map((message) => message(time)),
      { type: "restart", time },
    ];
  };
}

/**
 * Returns the copies of `input` with every order of the deadlines in its ties as `deadlineOrder`, each with its result:
 * an input whose result reached a tie with no entry left becomes, recursively, one input per deadline of the tie,
 * appended to `deadlineOrder` in entry order, so the first copy fires the first due deadline in each tie. `step` gives
 * the result of an input after the same parent; `unchosen` reads the deadlines of the first tie that the result reached
 * with no entry left.
 */
export function orderedInputs<R>(
  input: Input,
  step: (input: Input) => R,
  unchosen: (result: R) => readonly DeadlineId[] | undefined,
): { readonly input: Input; readonly result: R }[] {
  const result = step(input);
  const deadlines = unchosen(result);
  if (deadlines === undefined) return [{ input, result }];
  return deadlines.flatMap((d) =>
    orderedInputs({ ...input, deadlineOrder: [...(input.deadlineOrder ?? []), d] }, step, unchosen),
  );
}

/** An input after a parent, with its result. */
export interface Child {
  readonly input: Input;
  readonly result: Run;
}

/** The copies of an input with every order of the deadlines in its ties, each with its result after one parent. */
export type Ordered = (input: Input) => readonly Child[];

/**
 * Returns the `Ordered` function after the parent that `step` continues; a later call with an input of the same
 * `moveKey` reuses its children.
 */
export function orderedAfter(spec: Spec, step: (input: Input) => Run): Ordered {
  const made = new Map<string, readonly Child[]>();
  return (input) => {
    const key = moveKey(spec, input);
    const found = made.get(key);
    if (found !== undefined) return found;
    const children = orderedInputs(input, step, (run) => run.unchosenDeadlines);
    made.set(key, children);
    return children;
  };
}

const invalidInput: ReadonlySet<string> = new Set(invalidInputKinds);

/**
 * Returns whether the inputs appended after `parent` report no InvalidInput violation. test discards an appended input
 * that reports one, including the inputs that the order and choice comparisons run, because no caller or callee gives
 * such an input.
 */
export const givable = (parent: Run, result: Run): boolean =>
  !result.violationsSince(parent).some((v) => invalidInput.has(v.kind));
