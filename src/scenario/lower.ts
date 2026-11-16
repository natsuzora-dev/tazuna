import type { DefinitionRef } from "../data/definitionRef.ts";
import type {
  Expectation as DataExpectation,
  Line as DataLine,
  Fact,
  Hole,
  Origin,
  Template,
  ValueRef,
} from "../data/scenario.generated.ts";
import {
  createdMark,
  type DeadlineOf,
  type Expectation,
  factOf,
  type Line,
  lineIndex,
  observedRef,
  type ScenarioDefinition,
} from "./define.ts";

/** Why the lines of a scenario cannot be read as data. */
export type LoweringProblem =
  /** The value at `path` of the line or expectation is no definition that the spec names. */
  | { readonly kind: "unnamed"; readonly path: readonly (string | number)[] }
  /** A line was placed after When returned. */
  | { readonly kind: "lineAfterWhen" }
  /** The time of clock line `line` is not an instant in whole milliseconds. */
  | { readonly kind: "unparsableTime"; readonly line: number };

/** The lines and expectations of a scenario as data, with the call stack of each line. */
export interface Lowered {
  readonly lines: readonly DataLine[];
  readonly expectations: readonly DataExpectation[];
  readonly stacks: readonly (string | undefined)[];
  readonly problems: readonly LoweringProblem[];
}

/** The instant `time` in the trace's form, or undefined when it is none in whole milliseconds. */
export function instant(time: string): string | undefined {
  try {
    const t = Temporal.Instant.from(time);
    return t.epochNanoseconds % 1_000_000n === 0n ? t.toString() : undefined;
  } catch {
    return undefined;
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

const isRecord = (v: unknown): v is Record<PropertyKey, unknown> => typeof v === "object" && v !== null;

/** A placeholder that stands for the value that `ref` observes when the scenario runs. */
function observed(ref: ValueRef): unknown {
  return new Proxy(Object.create(null), {
    get: (_, key) =>
      key === observedRef ? ref : typeof key === "symbol" ? undefined : observed({ ...ref, path: [...ref.path, key] }),
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
    if (Array.isArray(v)) return v.map((x, i) => walk(x, [...path, String(i)]));
    return Object.fromEntries(Object.entries(v).map(([k, x]) => [k, walk(x, [...path, k])]));
  };
  return { value: walk(value, []), holes };
}

const factOfHandle = (handle: unknown): Fact => {
  if (isRecord(handle) && typeof handle[lineIndex] === "number")
    return { type: "line", index: handle[lineIndex] as number };
  return (handle as { [factOf]: Fact })[factOf];
};

const indexOf = (handle: unknown): number => (handle as Line)[lineIndex];

/**
 * Runs When with recording actors and Then on what When returned, and returns the lines and expectations as data.
 * `refOf` names a definition of the spec.
 */
export function lower(
  definition: ScenarioDefinition,
  refOf: (definition: unknown) => DefinitionRef | undefined,
): Lowered {
  const lines: DataLine[] = [];
  const stacks: (string | undefined)[] = [];
  const problems: LoweringProblem[] = [];
  let closed = false;
  const named = (d: unknown, path: readonly (string | number)[]): DefinitionRef => {
    const ref = refOf(d);
    if (ref === undefined) throw new Unnamed(path);
    return ref;
  };
  const at = () => ["lines", lines.length];

  const caused = (origin: Origin) => ({
    request: (target: unknown, pick?: { readonly input?: unknown }) => {
      const fact: Fact = {
        type: "request",
        origin,
        target: named(target, at()),
        ...(pick?.input === undefined ? {} : { input: pick.input }),
      };
      return { [factOf]: fact, target, input: observed({ fact, part: "input", path: [] }) };
    },
    event: (event: unknown, pick?: { readonly payload?: unknown }) => {
      const fact: Fact = {
        type: "event",
        origin,
        event: named(event, at()),
        ...(pick?.payload === undefined ? {} : { payload: pick.payload }),
      };
      return { [factOf]: fact, event, payload: observed({ fact, part: "input", path: [] }) };
    },
    screen: (screen: unknown) => ({
      [factOf]: { type: "screen", origin, screen: named(screen, at()) } satisfies Fact,
      screen,
    }),
    answer: (request: unknown) => {
      const fact: Fact = { type: "answer", origin, to: indexOf(request) };
      return { [factOf]: fact, output: observed({ fact, part: "output", path: [] }) };
    },
  });

  /** Places `line` and returns its handle, which `extra` extends. */
  const place = (line: DataLine, extra: (index: number) => object = () => ({})) => {
    if (closed) throw new LineAfterWhen();
    const index = lines.length;
    lines.push(line);
    stacks.push(new Error().stack);
    return { [lineIndex]: index, ...caused({ type: "line", index }), ...extra(index) };
  };
  const output = (fact: Fact) => ({ output: observed({ fact, part: "output", path: [] }) });
  const requestLine = (
    kind: "command" | "query" | "subscribe",
    target: unknown,
    input: unknown,
    more: { readonly peer?: string; readonly sameIdAs?: number },
  ) =>
    place(
      { type: "request", ...more, kind, target: named(target, at()), input: template(input) } as DataLine,
      (index) => ({ target, subscription: kind === "subscribe", ...output({ type: "line", index }) }),
    );

  const peerActor = (peer: string) => ({
    answer: (request: unknown, answer: unknown) => {
      const fact = factOfHandle(request);
      return place({ type: "answer", peer, request: fact, answer: template(answer) }, () => output(fact));
    },
    emit: (event: unknown, payload: unknown, options: { readonly resultOf: unknown }) =>
      place({
        type: "emit",
        peer,
        event: named(event, at()),
        payload: template(payload),
        ...(options.resultOf === null ? {} : { resultOf: factOfHandle(options.resultOf) }),
      }),
    leaveUnanswered: (request: unknown) => place({ type: "leaveUnanswered", peer, request: factOfHandle(request) }),
    send: (command: unknown, input: unknown) => requestLine("command", command, input, { peer }),
    call: (query: unknown, input: unknown) => requestLine("query", query, input, { peer }),
    subscribe: (query: unknown, input: unknown) => requestLine("subscribe", query, input, { peer }),
    unsubscribe: (subscription: unknown) => place({ type: "unsubscribe", peer, subscription: indexOf(subscription) }),
  });

  const w = {
    begin: caused({ type: "begin" }),
    client: {
      send: (command: unknown, input: unknown, options?: { readonly sameIdAs?: unknown }) =>
        requestLine(
          "command",
          command,
          input,
          options?.sameIdAs === undefined ? {} : { sameIdAs: indexOf(options.sameIdAs) },
        ),
      call: (query: unknown, input: unknown) => requestLine("query", query, input, {}),
      subscribe: (query: unknown, input: unknown) => requestLine("subscribe", query, input, {}),
      unsubscribe: (subscription: unknown) => place({ type: "unsubscribe", subscription: indexOf(subscription) }),
      resend: (line: { readonly target: unknown; readonly subscription: boolean }) =>
        place({ type: "resend", line: indexOf(line) }, (index) => ({
          target: line.target,
          subscription: line.subscription,
          ...output({ type: "line", index }),
        })),
    },
    user: {
      operate: (screen: unknown, control: string, payload?: unknown) =>
        place({ type: "operate", screen: factOfHandle(screen), control, payload: template(payload ?? {}) }),
      look: (screen: { readonly screen: unknown }) =>
        place({ type: "look", screen: factOfHandle(screen) }, () => ({ looked: screen.screen })),
    },
    peer: new Proxy({}, { get: (_, key) => (typeof key === "string" ? peerActor(key) : undefined) }) as Record<
      string,
      ReturnType<typeof peerActor>
    >,
    net: {
      deliver: (message: unknown) => place({ type: "deliver", message: factOfHandle(message) }),
      redeliver: (message: unknown) => place({ type: "redeliver", message: factOfHandle(message) }),
      lose: (message: unknown) => place({ type: "lose", message: factOfHandle(message) }),
      fail: (message: unknown) => place({ type: "fail", message: factOfHandle(message) }),
      inFlight: (message: unknown) => place({ type: "inFlight", message: factOfHandle(message) }),
    },
    clock: {
      at: (time: string, options?: { readonly order?: readonly DeadlineOf[] }) => {
        const t = instant(time);
        if (t === undefined) problems.push({ kind: "unparsableTime", line: lines.length });
        const order = (options?.order ?? []).map((d, k) => {
          const chart = named(d.chart, [...at(), "order", k]);
          return { service: chart.service, deadline: { instance: chart.name, state: d.state, name: d.name } };
        });
        return place({ type: "at", time: t ?? time, order });
      },
    },
    host: { restart: () => place({ type: "restart" }) },
  };

  const expectations: DataExpectation[] = [];
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
    const returned = definition.when(w as never);
    closed = true;
    (definition.expect as (lines: unknown) => readonly Expectation[])(returned).forEach((e, k) => {
      expectations.push(lowerExpectation(e, k));
    });
  } catch (error) {
    if (error instanceof Unnamed) problems.push({ kind: "unnamed", path: error.path });
    else if (error instanceof LineAfterWhen) problems.push({ kind: "lineAfterWhen" });
    else throw error;
  }
  return { lines, expectations, stacks, problems };
}
