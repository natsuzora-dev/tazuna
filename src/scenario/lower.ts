import type { z } from "zod";
import type { DefinitionRef } from "../data/definitionRef.ts";
import { collectionOf } from "../data/marks.ts";
import type {
  Expectation as DataExpectation,
  Line as DataLine,
  Fact,
  Hole,
  Origin,
  Template,
  ValueRef,
} from "../data/scenario.generated.ts";
import { schemaNode } from "../data/schemaNode.ts";
import type { Shape } from "../data/values.ts";
import type { AnyCommand, AnyEvent, AnyQuery, AnyScreen } from "../dsl/definition.ts";
import {
  type AnswerRef,
  type Caused,
  type ClientRequestLine,
  type ClientSubscribeLine,
  createdMark,
  type Delivered,
  type EndRef,
  type EventMessage,
  type Expectation,
  factOf,
  type Line,
  type Look,
  lineIndex,
  type Message,
  type OutRequest,
  type OutSubscription,
  observedRef,
  type ProcessingLine,
  rawMark,
  type ScenarioDefinition,
  type ScreenRef,
  type When,
  writtenAt,
} from "./define.ts";

/** How a scenario reads an observed value that exists only when the scenario runs. */
export type ObservedUse =
  /** It lists its fields: a spread, `Object.keys`, or a loop over it. */
  | "spread"
  /** It asks whether a field is present (`in`). */
  | "presence"
  /** It converts the value to a string or number: a template literal, arithmetic, or a comparison. */
  | "conversion"
  /** It reads a field that the value's schema does not have, such as an array method. */
  | "unknownField"
  /** It reads an element of a bag, set or sortedBy array by position, which means nothing there. */
  | "position";

/** Why the lines of a scenario cannot be read as data. */
export type LoweringViolation =
  /** The value at `path` of the line or expectation is no definition that the spec names. */
  | { readonly kind: "unnamed"; readonly path: readonly (string | number)[] }
  /** A line was placed after When returned. */
  | { readonly kind: "lineAfterWhen" }
  /** The time of clock line `line` is not an instant in whole milliseconds. */
  | { readonly kind: "unparsableTime"; readonly line: number }
  /** Line `line` uses an observed value in the way `use`, at the field `path`, instead of placing it whole. */
  | {
      readonly kind: "misusedObserved";
      readonly line: number;
      readonly use: ObservedUse;
      readonly path: readonly string[];
    };

export interface Lowered {
  readonly lines: readonly DataLine[];
  readonly expectations: readonly DataExpectation[];
  readonly stacks: readonly (string | undefined)[];
  readonly expectationStacks: readonly (string | undefined)[];
  readonly violations: readonly LoweringViolation[];
}

const documentedInstant = /^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:[0-5]\d(?:\.(?=\d)\d{0,3}0{0,6})?(?:Z|[+-]\d{2}:\d{2})$/;
const [earliest, end] = [
  Temporal.Instant.from("0000-01-01T00:00:00Z"),
  Temporal.Instant.from("+010000-01-01T00:00:00Z"),
];

/**
 * Lean's scenarioTime?, as Temporal.Instant.prototype.toString writes it: the time of a start or clock line in the form
 * that tazuna documents, with seconds, a fraction of up to nine digits, and `Z` or an offset `±HH:MM`. A fraction below
 * a millisecond, or a time outside years 0000 to 9999, has none.
 */
export function instant(time: string): string | undefined {
  if (!documentedInstant.test(time)) return undefined;
  try {
    const t = Temporal.Instant.from(time);
    return Temporal.Instant.compare(t, earliest) >= 0 && Temporal.Instant.compare(t, end) < 0
      ? t.toString()
      : undefined;
  } catch (error) {
    if (error instanceof RangeError) return undefined;
    throw error;
  }
}

class Unnamed extends Error {
  readonly path: readonly (string | number)[];
  constructor(path: readonly (string | number)[]) {
    super("unnamed definition");
    this.path = path;
  }
}

class LineAfterWhen extends Error {}

class Misused extends Error {
  readonly use: ObservedUse;
  readonly path: readonly string[];
  constructor(use: ObservedUse, path: readonly string[]) {
    super(`observed value used as ${use}`);
    this.use = use;
    this.path = path;
  }
}

const isRecord = (v: unknown): v is Record<PropertyKey, unknown> => typeof v === "object" && v !== null;

/** The schema of a value: an object of shape `Shape` at the top, a Zod schema below, or unknown. */
type Schema = { readonly shape: Shape } | z.ZodType | undefined;

function fieldOf(schema: Schema, key: string): { readonly schema: Schema } | ObservedUse {
  if (schema === undefined) return { schema: undefined };
  if ("shape" in schema && !("def" in schema))
    return Object.hasOwn(schema.shape, key) ? { schema: schema.shape[key] } : "unknownField";
  const node = schemaNode(schema as z.ZodType);
  switch (node.type) {
    case "optional":
    case "nullable":
    case "default":
      return fieldOf(node.inner, key);
    case "object":
      return Object.hasOwn(node.shape, key) ? { schema: node.shape[key] } : "unknownField";
    case "array":
      if (!/^(0|[1-9][0-9]*)$/.test(key)) return "unknownField";
      return collectionOf(schema as z.ZodType) === undefined ? { schema: node.element } : "position";
    default:
      return { schema: undefined };
  }
}

/**
 * A placeholder that stands for the value that `ref` observes when the scenario runs, of `schema`. It is placed whole:
 * reading a field of its schema gives the field's placeholder, and any other use throws.
 */
function observed(ref: ValueRef, schema: Schema): unknown {
  const misused = (use: ObservedUse): never => {
    throw new Misused(use, ref.path);
  };
  return new Proxy(Object.create(null), {
    get: (_, key) => {
      if (key === observedRef) return ref;
      if (key === Symbol.toPrimitive) return () => misused("conversion");
      if (typeof key === "symbol") return undefined;
      if (key === "toString" || key === "valueOf") return () => misused("conversion");
      const field = fieldOf(schema, key);
      if (typeof field === "string") return misused(field);
      return observed({ ...ref, path: [...ref.path, key] }, field.schema);
    },
    has: () => misused("presence"),
    ownKeys: () => misused("spread"),
  });
}

/** The template of a written value: its observed placeholders and `created()` markers become holes. */
function template(value: unknown): Template {
  const holes: Hole[] = [];
  const walk = (v: unknown, path: readonly string[]): unknown => {
    if (!isRecord(v)) return v;
    const ref = v[observedRef] as ValueRef | undefined;
    if (ref !== undefined) {
      holes.push({ path: [...path], fill: { type: "ref", value: ref } });
      return null;
    }
    if (v[createdMark] === true) {
      holes.push({ path: [...path], fill: { type: "created" } });
      return null;
    }
    if (rawMark in v) return v[rawMark];
    if (Array.isArray(v)) return v.map((x, i) => walk(x, [...path, String(i)]));
    return Object.fromEntries(Object.entries(v).map(([k, x]) => [k, walk(x, [...path, k])]));
  };
  return { value: walk(value, []), holes };
}

const factOfHandle = (handle: unknown): Fact => {
  if (isRecord(handle) && factOf in handle) return handle[factOf] as Fact;
  return { type: "line", index: indexOf(handle) };
};

const indexOf = (handle: unknown): number => (handle as Line)[lineIndex];

interface RequestShapes {
  readonly kind: "command" | "query";
  readonly input: Shape;
  readonly output?: Shape;
}

const shapeOf = (shape: Shape | undefined): Schema => (shape === undefined ? undefined : { shape });

/** The handle `o` as the type that When gives it; its brands exist only in types. */
const handle = <H>(o: object): H => o as H;

type Peers = ScenarioDefinition["given"]["peers"];

/**
 * Runs When with recording actors and Then on what When returned, and returns the lines and expectations as data.
 * `refOf` names a definition of the spec.
 */
export function lower(
  definition: ScenarioDefinition,
  refOf: (definition: unknown) => DefinitionRef | undefined,
  serviceOf: (contract: unknown) => string | undefined,
): Lowered {
  const lines: DataLine[] = [];
  const stacks: (string | undefined)[] = [];
  const violations: LoweringViolation[] = [];
  let closed = false;
  const named = (d: unknown, path: readonly (string | number)[]): DefinitionRef => {
    const ref = refOf(d);
    if (ref === undefined) throw new Unnamed(path);
    return ref;
  };
  const at = () => ["lines", lines.length];
  const serviceNamed = (contract: unknown, path: readonly (string | number)[]): string => {
    const service = serviceOf(contract);
    if (service === undefined) throw new Unnamed(path);
    return service;
  };
  const outputOf = (fact: Fact, target: unknown) =>
    observed({ fact, part: "output", path: [] }, shapeOf((target as RequestShapes | undefined)?.output));
  const requestMessage = (fact: Fact, target: unknown) => ({
    [factOf]: fact,
    target,
    input: observed({ fact, part: "input", path: [] }, shapeOf((target as RequestShapes).input)),
  });

  const caused = (origin: Origin): Caused => {
    const request = (subscribe: boolean) => (target: unknown, pick?: unknown) => {
      const fact: Fact = {
        type: "request",
        origin,
        kind: subscribe ? "subscribe" : (target as RequestShapes).kind,
        target: named(target, at()),
        ...(pick === undefined ? {} : { input: template(pick) }),
      };
      return requestMessage(fact, target);
    };
    return {
      request: <T extends AnyCommand | AnyQuery>(target: T, pick?: unknown) =>
        handle<OutRequest<T>>(request(false)(target, pick)),
      subscription: <Q extends AnyQuery>(query: Q, pick?: unknown) =>
        handle<OutSubscription<Q>>(request(true)(query, pick)),
      event: <Ev extends AnyEvent>(event: Ev, pick?: unknown, route?: { readonly to: unknown }) => {
        const fact: Fact = {
          type: "event",
          origin,
          event: named(event, at()),
          ...(pick === undefined ? {} : { payload: template(pick) }),
          ...(route === undefined ? {} : { receiver: serviceNamed(route.to, [...at(), "to"]) }),
        };
        const shape = (event as { readonly payload: Shape }).payload;
        return handle<EventMessage<Ev>>({
          [factOf]: fact,
          event,
          payload: observed({ fact, part: "input", path: [] }, { shape }),
        });
      },
      screen: <Sc extends AnyScreen>(screen: Sc) =>
        handle<ScreenRef<Sc>>({
          [factOf]: { type: "screen", origin, screen: named(screen, at()) } satisfies Fact,
          screen,
        }),
      answer: <T>(request: { readonly target: T }) => {
        const fact: Fact = { type: "answer", origin, to: indexOf(request) };
        return handle<AnswerRef<T>>({ [factOf]: fact, output: outputOf(fact, request.target) });
      },
      end: (subscription: unknown) =>
        handle<EndRef>({
          [factOf]: { type: "end", origin, subscription: factOfHandle(subscription) } satisfies Fact,
        }),
    };
  };

  const place = (line: DataLine): number => {
    if (closed) throw new LineAfterWhen();
    lines.push(line);
    stacks.push(new Error().stack);
    return lines.length - 1;
  };
  const processingLine = (line: DataLine) => {
    const index = place(line);
    return { [lineIndex]: index, ...caused({ type: "line", index }) };
  };
  const processing = (line: DataLine) => handle<ProcessingLine>(processingLine(line));
  const self = (index: number): Fact => ({ type: "line", index });
  const clientRequest = (
    kind: "command" | "query" | "subscribe",
    target: unknown,
    input: unknown,
    sameIdAs?: number,
  ) => {
    const handle = processingLine({
      type: "request",
      kind,
      target: named(target, at()),
      input: template(input),
      ...(sameIdAs === undefined ? {} : { sameIdAs }),
    });
    const index = handle[lineIndex];
    return { ...handle, target, subscribes: kind === "subscribe", output: outputOf(self(index), target) };
  };

  const peerActor = (peer: string) => {
    const stated = (line: DataLine) => {
      const index = place(line);
      return { [lineIndex]: index, [factOf]: self(index) };
    };
    const requestLine = (kind: "command" | "query" | "subscribe") => (target: unknown, input: unknown) => {
      const handle = stated({ type: "request", peer, kind, target: named(target, at()), input: template(input) });
      const index = handle[lineIndex];
      return {
        ...handle,
        ...requestMessage(self(index), target),
        subscribes: kind === "subscribe",
        output: outputOf(self(index), target),
      };
    };
    return {
      answer: (request: { readonly target: unknown }, answer: unknown) => {
        const handle = stated({ type: "answer", peer, request: factOfHandle(request), answer: template(answer) });
        return { ...handle, output: outputOf(self(handle[lineIndex]), request.target) };
      },
      emit: (event: unknown, payload: unknown, options: { readonly resultOf: unknown }) => {
        const ref = named(event, at());
        const handle = stated({
          type: "emit",
          peer,
          event: ref,
          payload: template(payload),
          ...(options.resultOf === null ? {} : { resultOf: factOfHandle(options.resultOf) }),
        });
        const origin: Origin = { type: "line", index: handle[lineIndex] };
        return {
          ...handle,
          to: (receiver: unknown) => ({
            [factOf]: {
              type: "event",
              origin,
              event: ref,
              receiver: serviceNamed(receiver, [...at(), "to"]),
            } satisfies Fact,
          }),
        };
      },
      leaveUnanswered: (request: unknown) => ({
        [lineIndex]: place({ type: "leaveUnanswered", peer, request: factOfHandle(request) }),
      }),
      send: requestLine("command"),
      call: requestLine("query"),
      subscribe: requestLine("subscribe"),
      unsubscribe: (subscription: unknown) =>
        stated({ type: "unsubscribe", peer, subscription: indexOf(subscription) }),
    };
  };

  const delivery = (line: DataLine, message: unknown) => {
    const handle = processingLine(line);
    const target = isRecord(message) ? message["target"] : undefined;
    return {
      ...handle,
      [factOf]: self(handle[lineIndex]),
      ...(target === undefined ? {} : { target, output: outputOf(self(handle[lineIndex]), target) }),
    };
  };

  const w = {
    startup: caused({ type: "startup" }),
    client: {
      send: <C extends AnyCommand>(command: C, input: unknown, options?: { readonly sameIdAs?: Line }) =>
        handle<ClientRequestLine<C>>(
          clientRequest(
            "command",
            command,
            input,
            options?.sameIdAs === undefined ? undefined : indexOf(options.sameIdAs),
          ),
        ),
      call: <Q extends AnyQuery>(query: Q, input: unknown) =>
        handle<ClientRequestLine<Q>>(clientRequest("query", query, input)),
      subscribe: <Q extends AnyQuery>(query: Q, input: unknown) =>
        handle<ClientSubscribeLine<Q>>(clientRequest("subscribe", query, input)),
      unsubscribe: (subscription: Line) => processing({ type: "unsubscribe", subscription: indexOf(subscription) }),
      resend: <L extends ClientRequestLine | ClientSubscribeLine>(line: L) => {
        const placed = processingLine({ type: "resend", line: indexOf(line) });
        return handle<L>({
          ...placed,
          target: line.target,
          subscribes: line.subscribes,
          output: outputOf(self(placed[lineIndex]), line.target),
        });
      },
    },
    user: {
      operate: (screen: unknown, control: string, payload?: unknown) =>
        processing({ type: "operate", screen: factOfHandle(screen), control, payload: template(payload ?? {}) }),
      look: <Sc extends AnyScreen>(screen: ScreenRef<Sc>) =>
        handle<Look<Sc>>({ [lineIndex]: place({ type: "look", screen: factOfHandle(screen) }), looked: screen.screen }),
    },
    // A peer's actor is the same for every peer kind: the simulation tells a running peer from an external one.
    peer: new Proxy(
      {},
      { get: (_, key) => (typeof key === "string" ? peerActor(key) : undefined) },
    ) as When<Peers>["peer"],
    net: {
      deliver: <M extends Message>(message: M) =>
        handle<Delivered<M>>(delivery({ type: "deliver", message: factOfHandle(message) }, message)),
      redeliver: <M extends Message>(message: M) =>
        handle<Delivered<M>>(delivery({ type: "redeliver", message: factOfHandle(message) }, message)),
      lose: (message: Message) =>
        handle<Line>({ [lineIndex]: place({ type: "lose", message: factOfHandle(message) }) }),
      refuse: (message: Message) => processing({ type: "refuse", message: factOfHandle(message) }),
      leaveInFlight: (message: Message) =>
        handle<Line>({ [lineIndex]: place({ type: "leaveInFlight", message: factOfHandle(message) }) }),
    },
    clock: {
      at: (time: string) => {
        const t = instant(time);
        if (t === undefined) violations.push({ kind: "unparsableTime", line: lines.length });
        return processing({ type: "at", time: t ?? time });
      },
    },
    host: { restart: () => processing({ type: "restart" }) },
  } satisfies When<Peers>;

  const expectations: DataExpectation[] = [];
  const expectationStacks: (string | undefined)[] = [];
  const lowerExpectation = (e: Expectation, k: number): DataExpectation => {
    switch (e.kind) {
      case "answered":
        return { type: "answered", line: indexOf(e.line), answers: e.answers.map(template) };
      case "emitted":
        return {
          type: "emitted",
          line: indexOf(e.line),
          events: e.events.map((ev, j) => ({
            event: named(ev.event, ["then", k, "events", j]),
            payload: template(ev.payload),
          })),
        };
      case "requested":
        return {
          type: "requested",
          line: indexOf(e.line),
          requests: e.requests.flatMap((q, j) =>
            q.kind === "end"
              ? []
              : [{ kind: q.kind, target: named(q.target, ["then", k, "requests", j]), input: template(q.input) }],
          ),
          ends: e.requests.flatMap((q) => (q.kind === "end" ? [factOfHandle(q.subscription)] : [])),
        };
      case "offered":
        return {
          type: "offered",
          look: indexOf(e.look),
          control: e.control,
          payload: template(e.payload),
          offered: e.offered,
        };
    }
  };
  try {
    const returned = definition.when(w);
    closed = true;
    (definition.expect as (lines: unknown) => readonly Expectation[])(returned).forEach((e, k) => {
      expectations.push(lowerExpectation(e, k));
      expectationStacks.push(e[writtenAt]);
    });
  } catch (error) {
    if (error instanceof Unnamed) violations.push({ kind: "unnamed", path: error.path });
    else if (error instanceof LineAfterWhen) violations.push({ kind: "lineAfterWhen" });
    else if (error instanceof Misused)
      violations.push({ kind: "misusedObserved", line: lines.length, use: error.use, path: error.path });
    else throw error;
  }
  return { lines, expectations, stacks, expectationStacks, violations };
}
