import { type DefinitionRef, sameRef } from "../data/definitionRef.ts";
import { expectFound, InternalError } from "../data/internalError.ts";
import { invalidInputKinds } from "../data/invalidInput.generated.ts";
import type { Fact, Line, Scenario, Template } from "../data/scenario.generated.ts";
import { blamesSenderKinds, type LineId, type RejectionKind } from "../data/trace.generated.ts";
import type { Json } from "../data/values.ts";
import type { Violation } from "../data/violation.ts";
import type { Named } from "../dsl/definition.ts";
import type { Spec } from "../load/load.ts";
import type { LoadedScenario } from "../load/scenarios.ts";
import { type Schema, type Service, schemaOf } from "../service/basic.ts";
import type { Processing } from "../service/chart/queue.ts";
import { sameLineId } from "../service/message.ts";
import { Halt } from "../service/state.ts";
import { type Message, stateOf, type World } from "../sim/network.ts";
import type { Cache } from "../sim/spec/cache.ts";
import { Coverage } from "../sim/spec/coverage.ts";
import type { Listener } from "../sim/spec/listener.ts";
import { executeSpec, executeSpecFrom } from "../sim/spec/simulate.ts";
import { domainOf, rootTree, treeValues } from "../spec/domains.ts";
import { type ExploreStructure, rejectionKinds, rejectionReasons } from "../spec/structure.ts";
import { type Enabled, enabled } from "./enabled.ts";
import { halted, worldFingerprint } from "./fingerprint.ts";
import { search, Visited } from "./search.ts";
import { stepOrderChanges } from "./stepOrders.ts";

export interface Executed {
  readonly world: World;
  readonly listeners: ReadonlyMap<string, Listener>;
}

/** The lines of one step of explore, which a path appends together: a message stated and the line delivering it. */
export type Move = readonly Line[];

/** Lean's Slot. */
type Slot =
  | { readonly kind: "answer"; readonly awaiting: Enabled["awaiting"][number]; readonly message: Message }
  | { readonly kind: "at"; readonly time: Temporal.Instant }
  | { readonly kind: "operate"; readonly operation: Enabled["operations"][number] }
  | { readonly kind: "unsubscribe"; readonly line: number }
  | { readonly kind: "request"; readonly definition: DefinitionRef; readonly query: boolean }
  | { readonly kind: "emit"; readonly peer: string; readonly event: DefinitionRef }
  | { readonly kind: "restart" };

const isRequest = (m: Message): boolean =>
  m.body.type === "command" || m.body.type === "query" || m.body.type === "subscribe";

/** Lean's awaits. */
const awaits = (w: World, own: string, id: LineId, m: Message): boolean =>
  m.sender === own &&
  sameLineId(m.id, id) &&
  (m.status === "inFlight" || m.status === "delivered") &&
  w.roles.get(m.receiver) === "external" &&
  isRequest(m);

/** Lean's ended. */
const ended = (w: World, own: string, id: LineId): boolean =>
  expectFound(`own service ${own}`, stateOf(w, own)).lines.some(
    (l) => l.dir === "out" && l.type === "unsubscribe" && sameLineId(l.to, id),
  );

/** Lean's openSubscription. */
const openSubscription = (own: string, lines: readonly Line[], l: Line, i: number): boolean =>
  l.type === "request" &&
  l.peer === undefined &&
  l.kind === "subscribe" &&
  l.target.service === own &&
  !lines.some((u) => u.type === "unsubscribe" && u.subscription === i);

/** Lean's times. */
function times(w: World, e: Enabled): Temporal.Instant[] {
  if (e.nextDeadline === undefined) return [];
  const d = Temporal.Instant.from(e.nextDeadline);
  return [d.subtract({ milliseconds: 1 }), d].filter((t) => Temporal.Instant.compare(w.now, t) <= 0);
}

/** Lean's slots. */
function slots(spec: Spec, st: Service, sc: Scenario, lines: readonly Line[], w: World, e: Enabled): Slot[] {
  const own = sc.service;
  const externals = sc.given.peers.flatMap((p) => (p.role === "external" ? [p.service] : []));
  const definitions = spec.structure.definitions;
  return [
    ...e.awaiting.flatMap((a): Slot[] => {
      if (ended(w, own, a.id)) return [];
      const message = w.messages.find((m) => awaits(w, own, a.id, m));
      return message === undefined ? [] : [{ kind: "answer", awaiting: a, message }];
    }),
    ...times(w, e).map((time): Slot => ({ kind: "at", time })),
    ...e.operations.map((operation): Slot => ({ kind: "operate", operation })),
    ...lines.flatMap((l, i): Slot[] => (openSubscription(own, lines, l, i) ? [{ kind: "unsubscribe", line: i }] : [])),
    ...definitions.flatMap((d): Slot[] =>
      d.service === own && (d.kind === "command" || d.kind === "query")
        ? [{ kind: "request", definition: { service: d.service, name: d.name }, query: d.kind === "query" }]
        : [],
    ),
    ...definitions.flatMap((d): Slot[] => {
      const event = { service: d.service, name: d.name };
      return d.kind === "event" && externals.includes(d.service) && st.receives.some((r) => sameRef(r, event))
        ? [{ kind: "emit", peer: d.service, event }]
        : [];
    }),
    { kind: "restart" },
  ];
}

const literal = (value: Json): Template => ({ value, holes: [] });

/** Lean's requestFact?. */
function requestFact(m: Message): Fact {
  const { body } = m;
  if (body.type !== "command" && body.type !== "query" && body.type !== "subscribe")
    throw new InternalError(`request of ${JSON.stringify(m.id)}`);
  return {
    type: "request",
    origin: m.origin,
    kind: body.type,
    target: body.target,
    input: literal(body.input as Json),
  };
}

/** Lean's rejectedAnswer. */
const rejectedAnswer = (kind: RejectionKind, reason?: string): Json => ({
  result: "rejected",
  rejection: reason === undefined ? { kind } : { kind, reason },
});

/** Lean's rejections. */
const rejections = (reasons: readonly string[], kind: RejectionKind): Json[] =>
  kind === "requires" ? reasons.map((reason) => rejectedAnswer(kind, reason)) : [rejectedAnswer(kind)];

/** Lean's answerOf. */
const answerOf = (query: boolean, hasOutput: boolean, output: Json): Json =>
  query ? { result: "fulfilled", output } : hasOutput ? { result: "accepted", output } : { result: "accepted" };

/** Lean's answerMove. */
const answerMove = (receiver: string, request: Fact, answer: Json, delivering: boolean, k: number): Move =>
  delivering
    ? [
        { type: "deliver", message: request },
        { type: "answer", peer: receiver, request, answer: literal(answer) },
        { type: "deliver", message: { type: "line", index: k + 1 } },
      ]
    : [
        { type: "answer", peer: receiver, request, answer: literal(answer) },
        { type: "deliver", message: { type: "line", index: k } },
      ];

/** Lean's requestMoves. */
const requestMoves = (target: DefinitionRef, query: boolean, input: Json): Move[] =>
  (query ? (["query", "subscribe"] as const) : (["command"] as const)).map((kind) => [
    { type: "request", kind, target, input: literal(input) },
  ]);

/** Lean's exploreOf: the `explore()` of `service`, which load guarantees for a service with scenarios. */
export const exploreOf = (spec: Spec, service: string): ExploreStructure =>
  expectFound(
    `explore of ${service}`,
    spec.structure.explores.find((x) => x.service === service),
  );

/** Lean's RejectionKind.blamesSender. */
const blamesSender: ReadonlySet<RejectionKind> = new Set(blamesSenderKinds);

/** Lean's answers. */
const answers = (
  query: boolean,
  outputs: readonly Json[] | undefined,
  kinds: readonly RejectionKind[],
  reasons: readonly string[],
): Json[] => [
  ...(outputs === undefined ? [answerOf(query, false, {})] : outputs.map((o) => answerOf(query, true, o))),
  ...kinds.filter((k) => !blamesSender.has(k)).flatMap((k) => rejections(reasons, k)),
];

/** Lean's fill, with the own service's declared domains. */
function fill(
  spec: Spec,
  domains: ExploreStructure["domains"],
  r: Processing,
  sc: Scenario,
  lines: readonly Line[],
  w: World,
  slot: Slot,
): Move[] {
  const { st } = r;
  const own = sc.service;
  const values = (schema: Schema) => {
    const tree = rootTree(domainOf(domains, schema), schemaOf(st, schema));
    if (!tree.ok)
      throw new InternalError(`no domain of ${JSON.stringify(schema)} at ${JSON.stringify(tree.undeclared)}`);
    return treeValues(tree.tree);
  };
  switch (slot.kind) {
    case "answer": {
      const { awaiting: a, message: m } = slot;
      const request = requestFact(m);
      const target = { service: a.target, name: a.name };
      const d = expectFound(
        `definition ${target.service}.${target.name}`,
        spec.structure.definitions.find((x) => sameRef(x, target)),
      );
      if (d.kind !== "command" && d.kind !== "query")
        throw new InternalError(`${target.service}.${target.name} is no command or query`);
      const outputs = d.output === null ? undefined : values({ kind: "output", definition: target });
      return answers(
        d.kind === "query",
        outputs,
        rejectionKinds(spec.structure, own, target),
        rejectionReasons(spec.structure, target),
      ).map((answer) => answerMove(m.receiver, request, answer, m.status === "inFlight", lines.length));
    }
    case "at":
      return [[{ type: "at", time: slot.time.toString() }]];
    case "operate": {
      const o = slot.operation;
      const opened = expectFound(
        `opening of ${JSON.stringify(o.id)}`,
        w.opened.findLast((s) => s.service === own && s.id === o.id),
      );
      const screen = { service: own, name: o.screen };
      const payloads =
        o.payloads === null ? values({ kind: "control", screen, control: o.control }) : (o.payloads as Json[]);
      return payloads.map(
        (payload): Move => [
          {
            type: "operate",
            screen: { type: "screen", origin: opened.origin, screen },
            control: o.control,
            payload: literal(payload),
          },
        ],
      );
    }
    case "unsubscribe":
      return [[{ type: "unsubscribe", subscription: slot.line }]];
    case "request":
      return values({ kind: "input", definition: slot.definition }).flatMap((input) =>
        requestMoves(slot.definition, slot.query, input),
      );
    case "emit":
      return values({ kind: "payload", event: slot.event }).map(
        (payload): Move => [
          { type: "emit", peer: slot.peer, event: slot.event, payload: literal(payload) },
          {
            type: "deliver",
            message: { type: "event", origin: { type: "line", index: lines.length }, event: slot.event, receiver: own },
          },
        ],
      );
    case "restart":
      return [[{ type: "restart" }]];
  }
}

/**
 * Lean's moves: returns a function that lists the moves after an executed world, each slot filled. It halts with the
 * fault of what the own service enables.
 */
export const enabledLines = (spec: Spec, sc: Scenario) => {
  const { domains } = exploreOf(spec, sc.service);
  return (lines: readonly Line[], { world: w }: Executed): Move[] => {
    const r = expectFound(`own service ${sc.service}`, w.services.get(sc.service)).processing;
    const e = enabled(r);
    return r.evaluations.quietly(() =>
      slots(spec, r.st, sc, lines, w, e).flatMap((slot) => fill(spec, domains, r, sc, lines, w, slot)),
    );
  };
};

export const executeAppended = (spec: Spec, sc: Scenario, appended: readonly Line[], cache?: () => Cache): Executed =>
  executeSpec(spec, appended.length === 0 ? sc : { ...sc, lines: [...sc.lines, ...appended] }, [], cache);

/**
 * The execution of the scenario with `appended` and `move` after its lines, continued from `parent`, the execution with
 * `appended`. The plain method is executeAppended, which replays every line.
 */
export const executeMove = (
  spec: Spec,
  sc: Scenario,
  appended: readonly Line[],
  parent: Executed,
  move: Move,
): Executed =>
  executeSpecFrom(
    spec,
    { ...sc, lines: [...sc.lines, ...appended, ...move] },
    parent,
    sc.lines.length + appended.length,
  );

const invalidInput: ReadonlySet<string> = new Set(invalidInputKinds);

/**
 * The violations of each running service of `child` that its execution added after the execution of `parent`: its own, those its
 * listener collected, and its halt.
 */
function violationsSince(parent: Executed, child: Executed): Violation[] {
  return [...child.world.services].flatMap(([service, p]) => {
    const before = parent.world.services.get(service);
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

/**
 * Returns whether the lines appended after `parent` are lines that someone could write: no report of the simulation
 * and no InvalidInput violation of a running service. explore discards the others.
 */
const givable = (parent: Executed, child: Executed): boolean =>
  child.world.violations.length === parent.world.violations.length &&
  (child.world.halted === undefined || parent.world.halted !== undefined) &&
  !violationsSince(parent, child).some((v) => invalidInput.has(v.kind));

interface FoundOnPath {
  readonly violation: Violation;
  readonly appended: readonly Line[];
}

export interface ExploredLines {
  readonly found: readonly FoundOnPath[];
  /** What the scenario's execution and every path reached, except an execution that halted. */
  readonly reached: Coverage;
  /** How many worlds the search visited, by fingerprint. */
  readonly visited: number;
}

/**
 * Adds what `executed` reached and `parent`, the execution it continues, had not: what its path reports (Space.out),
 * not what the path before it already reported, as merged_search_reports takes a report.
 */
const coverageOf = (executed: Executed, reached: Coverage, parent?: Executed) => {
  if (halted(executed.world)) return;
  for (const [service, l] of executed.listeners) reached.addAll(l.coverage, parent?.listeners.get(service)?.coverage);
};

/**
 * Explores the scenario: executes its lines, and the paths that append moves that face the own service, up to the depth
 * of its service's `explore()`, breadth-first, without extending a path whose world an earlier path reached, discarding
 * a path whose last line no one could write (givable). Returns the violations of the running services that each path
 * added, the step orders of its last move's processings that change their result, and what the executions reached.
 */
export function exploreLines(spec: Spec, named: Named<LoadedScenario>): ExploredLines {
  const sc = named.definition.scenario;
  const base = executeAppended(spec, sc, []);
  const found: FoundOnPath[] = [];
  const reached = new Coverage();
  coverageOf(base, reached);
  if (halted(base.world) || base.world.violations.length > 0) return { found, reached, visited: 0 };
  const enabledAfter = enabledLines(spec, sc);
  const next = (path: readonly Move[], executed: Executed): Move[] => {
    if (halted(executed.world)) return [];
    try {
      return enabledAfter([...sc.lines, ...path.flat()], executed);
    } catch (error) {
      // What the own service enables next is evaluated after the path, so a Fault there is the path's.
      if (!(error instanceof Halt)) throw error;
      found.push({ violation: error.violation, appended: path.flat() });
      return [];
    }
  };
  const step = (parent: Executed, path: readonly Move[]): Executed | undefined => {
    const child = executeMove(
      spec,
      sc,
      path.slice(0, -1).flat(),
      parent,
      expectFound("the last move of a path", path.at(-1)),
    );
    return givable(parent, child) ? child : undefined;
  };
  const visited = new Visited();
  for (const { path, result, parent } of search<Move, Executed>({
    start: { path: [], result: base },
    bound: exploreOf(spec, sc.service).depth,
    step,
    next,
    merge: { fingerprint: (executed) => worldFingerprint(executed.world), visited },
  })) {
    if (parent === undefined) continue;
    const appended = path.flat();
    coverageOf(result, reached, parent);
    for (const violation of violationsSince(parent, result)) found.push({ violation, appended });
    const from = sc.lines.length + path.slice(0, -1).flat().length;
    for (const violation of stepOrderChanges(spec, { ...sc, lines: [...sc.lines, ...appended] }, result, from))
      found.push({ violation, appended });
  }
  return { found, reached, visited: visited.size };
}
