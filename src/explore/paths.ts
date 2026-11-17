import { invalidInputKinds } from "../data/invalidInput.generated.ts";
import type { Fact, Line, Scenario, Template } from "../data/scenario.generated.ts";
import type { Answer } from "../data/trace.generated.ts";
import { canonicalJson, type Shape } from "../data/values.ts";
import type { Violation } from "../data/violation.ts";
import type { AnyCommand, AnyEvent, AnyQuery, ChartSpec, Named } from "../dsl/definition.ts";
import type { Spec } from "../load/load.ts";
import type { LoadedScenario } from "../load/scenarios.ts";
import { serviceOf } from "../service/basic.ts";
import { Halt } from "../service/state.ts";
import { type Message, stateOf, type World } from "../sim/network.ts";
import { Coverage } from "../sim/spec/coverage.ts";
import { fingerprint } from "../sim/spec/fingerprint.ts";
import type { Listener } from "../sim/spec/listener.ts";
import { executeSpec } from "../sim/spec/simulate.ts";
import { refOfTraceName, rejectionKinds, traceNameOfRef } from "../spec/structure.ts";
import { enabled } from "./enabled.ts";
import { search } from "./search.ts";
import { stepOrderChanges } from "./stepOrders.ts";
import { stringsIn, valuesFor } from "./values.ts";

export interface Executed {
  readonly world: World;
  readonly listeners: ReadonlyMap<string, Listener>;
}

/** The values that the scenarios of a spec already write, tried first, by `<service>.<name>` of a definition. */
export interface Seen {
  readonly words: readonly string[];
  readonly answers: ReadonlyMap<string, readonly unknown[]>;
  /** The inputs of the requests and the payloads of the events that lines write. */
  readonly messages: ReadonlyMap<string, readonly unknown[]>;
  /** The payloads of the operations, by `<service>.<screen>.<control>`. */
  readonly payloads: ReadonlyMap<string, readonly unknown[]>;
}

const nameOf = (r: { readonly service: string; readonly name: string }) => `${r.service}.${r.name}`;

export function seenLines(spec: Spec): Seen {
  const words = new Set<string>();
  const answers = new Map<string, unknown[]>();
  const messages = new Map<string, unknown[]>();
  const payloads = new Map<string, unknown[]>();
  const add = (map: Map<string, unknown[]>, key: string, t: Template) => {
    map.set(key, [...(map.get(key) ?? []), t.value]);
    for (const w of stringsIn(t.value)) words.add(w);
  };
  for (const s of spec.scenarios)
    for (const l of (s.definition as LoadedScenario).scenario.lines)
      switch (l.type) {
        case "request":
          add(messages, nameOf(l.target), l.input);
          break;
        case "emit":
          add(messages, nameOf(l.event), l.payload);
          break;
        case "answer":
          if (l.request.type === "request") add(answers, nameOf(l.request.target), l.answer);
          break;
        case "operate":
          if (l.screen.type === "screen") add(payloads, `${nameOf(l.screen.screen)}.${l.control}`, l.payload);
          break;
      }
  return { words: [...words], answers, messages, payloads };
}

const literal = (value: unknown): Template => ({ value, holes: [] });

const reject: Answer = { result: "rejected", rejection: { kind: "unavailable" } };

const isAnswer = (v: unknown): v is Answer =>
  typeof v === "object" && v !== null && "result" in v && typeof (v as { result: unknown }).result === "string";

function awaitedMessage(w: World, own: string, id: string): Message | undefined {
  return w.messages.find(
    (m) =>
      m.sender === own &&
      m.id === id &&
      (m.status === "inFlight" || m.status === "delivered") &&
      w.roles.get(m.receiver) === "external" &&
      (m.body.type === "command" || m.body.type === "query" || m.body.type === "subscribe"),
  );
}

/** The fact that names the request `m` by its origin, its kind, its target, and its whole input. */
function requestFact(m: Message): Fact | undefined {
  if (m.body.type !== "command" && m.body.type !== "query" && m.body.type !== "subscribe") return undefined;
  return {
    type: "request",
    origin: m.origin,
    kind: m.body.type,
    target: refOfTraceName(m.sender, m.body.name),
    input: literal(m.body.input),
  };
}

/** The lines of one step of explore, which a path appends together: a message stated and the line delivering it. */
export type Move = readonly Line[];

/**
 * Returns a function that lists the moves that may come next after an executed world, all facing the own service: a
 * client's request to each of its commands and queries, a subscription's end for each subscription a client line opened
 * and no line ended, an external peer's answer to each request the own service awaits from it (delivering the request
 * first when it is in flight) and each event of an external peer that the own service receives, each delivered to the
 * own service, an operation of each open screen, the clock just before and at the next deadline, and a restart. A
 * running peer's messages stay as the scenario left them.
 */
export function enabledLines(
  spec: Spec,
  sc: Scenario,
  seen: Seen,
  valuesPerInput: number,
): (lines: readonly Line[], executed: Executed) => Move[] {
  const own = sc.service;
  const values = (key: string, shape: Shape) =>
    valuesFor(shape, seen.messages.get(key) ?? [], seen.words, valuesPerInput);
  const externals = sc.given.peers.flatMap((p) => (p.role === "external" ? [p.service] : []));
  const requests = spec.definitions.flatMap(({ service, name, definition: d }): Line[] => {
    if (service !== own) return [];
    const target = { service, name };
    const request = (kind: "command" | "query" | "subscribe", input: unknown): Line => ({
      type: "request",
      kind,
      target,
      input: literal(input),
    });
    if (d.kind === "command")
      return values(nameOf(target), (d as AnyCommand).input).map((input) => request("command", input));
    if (d.kind === "query")
      return values(nameOf(target), (d as AnyQuery).input).flatMap((input) => [
        request("query", input),
        request("subscribe", input),
      ]);
    return [];
  });
  const receives = serviceOf(spec.structure, own).receives;
  const events = spec.definitions.flatMap(({ service, name, definition: d }): Line[] => {
    const event = { service, name };
    if (d.kind !== "event" || !externals.includes(service) || !receives.includes(traceNameOfRef(event, own))) return [];
    return values(nameOf(event), (d as AnyEvent).payload).map(
      (payload): Line => ({ type: "emit", peer: service, event, payload: literal(payload) }),
    );
  });
  return (lines, { world: w }) => {
    const self = (k: number): Fact => ({ type: "line", index: lines.length + k });
    const r = w.participants.get(own)?.processing;
    if (r === undefined) return [];
    const next = enabled(r);
    const ownLines = stateOf(w, own)?.lines ?? [];
    const ended = new Set(ownLines.flatMap((l) => (l.dir === "out" && l.type === "unsubscribe" ? [l.to] : [])));
    const answers = next.awaiting.flatMap((a) => {
      const m = ended.has(a.id) ? undefined : awaitedMessage(w, own, a.id);
      const request = m === undefined ? undefined : requestFact(m);
      const target = spec.definitions.find(
        (d) =>
          d.service === a.target &&
          d.name === a.name &&
          (d.definition.kind === "command" || d.definition.kind === "query"),
      )?.definition as AnyCommand | AnyQuery | undefined;
      if (m === undefined || request === undefined || target === undefined) return [];
      const output = target.output as Shape | undefined;
      const generated = (output === undefined ? [{}] : valuesFor(output, [], seen.words, valuesPerInput)).map(
        (o): Answer =>
          target.kind === "query"
            ? { result: "fulfilled", output: o }
            : output === undefined
              ? { result: "accepted" }
              : { result: "accepted", output: o },
      );
      const listed = (seen.answers.get(`${a.target}.${a.name}`) ?? []).filter(isAnswer);
      const kinds = rejectionKinds(spec.structure, own, { service: a.target, name: a.name });
      const pool = new Map<string, Answer>();
      for (const answer of [
        listed[0] ?? generated[0],
        ...(kinds.includes("unavailable") ? [reject] : []),
        ...listed,
        ...generated,
      ])
        if (answer !== undefined) pool.set(canonicalJson(answer), answer);
      const delivering: Line[] = m.status === "inFlight" ? [{ type: "deliver", message: request }] : [];
      return [...pool.values()]
        .slice(0, valuesPerInput)
        .map(
          (answer): Move => [
            ...delivering,
            { type: "answer", peer: m.receiver, request, answer: literal(answer) },
            { type: "deliver", message: self(delivering.length) },
          ],
        );
    });
    const times =
      next.nextDeadline === undefined
        ? []
        : [
            Temporal.Instant.from(next.nextDeadline).subtract({ milliseconds: 1 }),
            Temporal.Instant.from(next.nextDeadline),
          ]
            .filter((t) => Temporal.Instant.compare(t, w.now) >= 0)
            .map((t): Line => ({ type: "at", time: t.toString() }));
    const operations = next.operations.flatMap((o) => {
      const opened = w.opened.findLast(
        (s) => s.service === own && s.chart === o.screen && r.state.stack.includes(s.resource),
      );
      const screen = spec.definitions.find(
        (d) => d.service === own && d.name === o.screen && d.definition.kind === "screen",
      );
      if (opened === undefined || screen === undefined) return [];
      const shape = ((screen.definition as unknown as ChartSpec).controls?.[o.control]?.payload ?? {}) as Shape;
      const listed = seen.payloads.get(`${own}.${o.screen}.${o.control}`) ?? [];
      const payloads =
        o.payloads === "any"
          ? valuesFor(shape, listed, seen.words, valuesPerInput)
          : o.payloads.slice(0, valuesPerInput);
      return payloads.map(
        (payload): Line => ({
          type: "operate",
          screen: { type: "screen", origin: opened.origin, screen: { service: own, name: o.screen } },
          control: o.control,
          payload: literal(payload),
        }),
      );
    });
    const unsubscribes = lines.flatMap((l, i): Line[] =>
      l.type === "request" &&
      l.kind === "subscribe" &&
      l.peer === undefined &&
      l.target.service === own &&
      !lines.some((u) => u.type === "unsubscribe" && u.subscription === i)
        ? [{ type: "unsubscribe", subscription: i }]
        : [],
    );
    const emitted = events.map((line): Move => {
      const event = line.type === "emit" ? line.event : { service: "", name: "" };
      return [
        line,
        {
          type: "deliver",
          message: { type: "event", origin: { type: "line", index: lines.length }, event, receiver: own },
        },
      ];
    });
    return [
      ...answers,
      ...[...times, ...operations, ...unsubscribes, ...requests].map((line): Move => [line]),
      ...emitted,
      [{ type: "restart" }],
    ];
  };
}

export const executeAppended = (spec: Spec, sc: Scenario, appended: readonly Line[]): Executed =>
  executeSpec(spec, appended.length === 0 ? sc : { ...sc, lines: [...sc.lines, ...appended] });

const invalidInput: ReadonlySet<string> = new Set(invalidInputKinds);

/**
 * The violations of each participant of `child` that its execution added after the execution of `parent`: its own, those its
 * listener collected, and its halt.
 */
function violationsSince(parent: Executed, child: Executed): Violation[] {
  return [...child.world.participants].flatMap(([service, p]) => {
    const before = parent.world.participants.get(service);
    const was = before?.processing.state.violations.length ?? 0;
    const collected = child.listeners.get(service)?.collected.violations ?? [];
    const collectedWas = parent.listeners.get(service)?.collected.violations.length ?? 0;
    return [
      ...p.processing.state.violations.slice(was),
      ...collected.slice(collectedWas),
      ...(p.halted !== undefined && before?.halted === undefined ? [p.halted] : []),
    ];
  });
}

const halted = (w: World): boolean =>
  w.halted !== undefined || [...w.participants.values()].some((p) => p.halted !== undefined);

/**
 * Returns whether the lines appended after `parent` are lines that someone could write: no report of the simulation
 * and no InvalidInput violation of a participant. explore discards the others.
 */
const givable = (parent: Executed, child: Executed): boolean =>
  child.world.violations.length === parent.world.violations.length &&
  (child.world.halted === undefined || parent.world.halted !== undefined) &&
  !violationsSince(parent, child).some((v) => invalidInput.has(v.kind));

/** The state of a world that explore merges paths by: each participant's and the messages in flight. */
function worldFingerprint(w: World): string {
  return canonicalJson([
    halted(w),
    w.now.toString(),
    [...w.participants].map(([service, p]) => [service, fingerprint(p.processing)]),
    w.messages.flatMap((m) => (m.status === "inFlight" ? [[m.sender, m.receiver, m.body as never]] : [])),
  ]);
}

export const valuesPerPayload = 2;

export interface Bounds {
  /** The maximum number of lines appended to a scenario. */
  readonly depth: number;
  readonly valuesPerPayload: number;
}

interface FoundOnPath {
  readonly violation: Violation;
  readonly appended: readonly Line[];
}

export interface ExploredLines {
  readonly found: readonly FoundOnPath[];
  /** The lines each path appended, breadth-first. */
  readonly paths: readonly (readonly Line[])[];
  /** What the scenario's execution and every path reached, except an execution that halted. */
  readonly reached: Coverage;
}

const coverageOf = (executed: Executed, reached: Coverage) => {
  if (halted(executed.world)) return;
  for (const l of executed.listeners.values()) reached.addAll(l.coverage);
};

/**
 * Explores the scenario: executes its lines, and the paths that append up to `depth` lines that face the own service,
 * breadth-first, without extending a path whose world an earlier path reached, discarding a path whose last line no one
 * could write (givable). Returns the violations of the participants that each path added, the step orders of its last
 * move's processings that change their result, and what the executions reached.
 */
export function exploreLines(spec: Spec, named: Named<LoadedScenario>, seen: Seen, bounds: Bounds): ExploredLines {
  const sc = named.definition.scenario;
  const base = executeAppended(spec, sc, []);
  const found: FoundOnPath[] = [];
  const paths: (readonly Line[])[] = [];
  const reached = new Coverage();
  coverageOf(base, reached);
  if (halted(base.world) || base.world.violations.length > 0) return { found, paths, reached };
  const enabledAfter = enabledLines(spec, sc, seen, bounds.valuesPerPayload);
  const children = new Map<Executed, Map<Move, Executed>>();
  const next = (path: readonly Move[], executed: Executed): Move[] => {
    if (halted(executed.world)) return [];
    const appended = path.flat();
    const made = new Map<Move, Executed>();
    let moves: Move[];
    try {
      moves = enabledAfter([...sc.lines, ...appended], executed);
    } catch (error) {
      // What the own service enables next is evaluated after the path, so a Fault there is the path's.
      if (!(error instanceof Halt)) throw error;
      found.push({ violation: error.violation, appended });
      return [];
    }
    for (const move of moves) {
      const child = executeAppended(spec, sc, [...appended, ...move]);
      if (givable(executed, child)) made.set(move, child);
    }
    if (made.size > 0) children.set(executed, made);
    return [...made.keys()];
  };
  const step = (parent: Executed, move: Move): Executed => {
    const made = children.get(parent) as Map<Move, Executed>;
    const executed = made.get(move) as Executed;
    made.delete(move);
    if (made.size === 0) children.delete(parent);
    return executed;
  };
  for (const { path, result, parent } of search<Move, Executed>({
    start: { path: [], result: base },
    bound: bounds.depth,
    step,
    next,
    merge: { fingerprint: (executed) => worldFingerprint(executed.world) },
  })) {
    if (parent === undefined) continue;
    const appended = path.flat();
    paths.push(appended);
    coverageOf(result, reached);
    for (const violation of violationsSince(parent, result)) found.push({ violation, appended });
    const from = sc.lines.length + path.slice(0, -1).flat().length;
    for (const violation of stepOrderChanges(spec, { ...sc, lines: [...sc.lines, ...appended] }, result, from))
      found.push({ violation, appended });
  }
  return { found, paths, reached };
}
