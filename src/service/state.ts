import type { DefinitionRef } from "../data/definitionRef.ts";
import type { Fault } from "../data/fault.generated.ts";
import type { InvalidInput } from "../data/invalidInput.generated.ts";
import { limits } from "../data/limits.generated.ts";
import type { Activity, Requester, StepName } from "../data/step.generated.ts";
import { Subscriptions } from "../data/subscriptions.ts";
import type { Answer, LineId } from "../data/trace.generated.ts";
import { operationName } from "../data/trace.ts";
import type { Fields, Json } from "../data/values.ts";
import { type Located, type Location, type Violation, type ViolationError, withExtra } from "../data/violation.ts";
import { traceNameOfRef } from "../spec/structure.ts";
import { descendants, pathOf } from "../spec/tree.ts";
import { ref, type Service } from "./basic.ts";
import type { Chart, Transition } from "./chart/basic.ts";
import {
  type Access,
  Failed,
  type Functions,
  givenKeys,
  type Holder,
  holderId,
  type Keys,
  type Scope,
} from "./functions.ts";
import type { CommandAnswers } from "./idempotency.ts";
import { chartOf, copyId, type InstanceId, mapOf, ownerId } from "./instance.ts";
import { type Halting, halts, idKey, type Line, type LineBody, type LineKind, type RequestBody } from "./message.ts";
import type { Note } from "./note.ts";
import type { Records, Row } from "./records.ts";

/**
 * TS only: the evaluation cache, which hears reads and writes through the note. An evaluation of `part` of the instance
 * `id` (its always transitions, or the items of a map state) is fresh while none of the names it read has been
 * written since.
 */
export interface Evaluations {
  /**
   * Returns whether the evaluation is fresh; when it is, the evaluations being tracked and the note hear its reads
   * again.
   */
  replayIfFresh(id: InstanceId, part: string): boolean;
  /** Returns the names that `f` reads, in first-read order. */
  track(f: () => void): string[];
  /**
   * Stores an evaluation whose `reads` are heard again while it is fresh; a write to any of `watched` makes it stale.
   */
  remember(id: InstanceId, part: string, reads: readonly string[], watched: readonly string[]): void;
  /** Runs `f` so that neither the evaluations being tracked nor the note hear its reads. */
  quietly<T>(f: () => T): T;
}

/**
 * The State, and what Lean passes beside it where it queues no work: the service (Lean's `st`), the spec functions
 * (Lean's `fs`), and the note. Only TS has `evaluations`, the run's listener, which hears writes through `note`, and
 * `place`, the location of violations of the service's invariants.
 */
export interface Run {
  readonly state: State;
  readonly st: Service;
  readonly functions: Functions;
  readonly note: Note;
  readonly evaluations: Evaluations;
  readonly place: Location | undefined;
}

/** The Access through which a Scope question tells `r.note` the values its expressions read and assign. */
export class NoteAccess implements Access {
  private readonly r: Run;
  private readonly scope: Scope;

  constructor(r: Run, scope: Scope) {
    this.r = r;
    this.scope = scope;
  }

  context(holder: Holder, field: string): void {
    this.r.note.readContext(holderId(this.scope, holder), field);
  }

  active(holder: Holder, state: string): void {
    this.r.note.readStates([[holderId(this.scope, holder), state]]);
  }

  assigned(holder: Holder, field: string): void {
    this.r.note.wroteContext(holderId(this.scope, holder), field);
  }

  shown(slot: string): void {
    this.r.note.readShown(holderId(this.scope, "owner"), slot);
  }

  now(): void {
    this.r.note.readNow();
  }
}

/** Runs `work` and tells the instrumentation that step `step` begins and ends. */
export function inStep(r: Run, step: number, name: StepName, started: InstanceId | undefined, work: () => void): void {
  r.note.stepBegins(step, name, started);
  try {
    work();
  } finally {
    r.note.stepEnds();
  }
}

/**
 * An instance of a machine or screen, or a copy of a map state. A machine, or a screen that no other screen opens, has
 * one instance per definition; `opens` creates an instance each time it opens a screen.
 */
export interface Instance {
  readonly chart: Chart;
  readonly id: InstanceId;
  context: Fields;
  readonly input: Fields;
  /** The active states and their entry times, in entry order. */
  readonly entered: Map<string, number>;
  /** For each parent, the children that were active when the parent last exited. */
  readonly lastChildren: Map<string, string[]>;
  /** Whether the instance entered a root final state and stopped. */
  closed: boolean;
  /**
   * The finished states that await onDone, in finishing order, set from when the onDone work is queued until it ends.
   */
  awaitingOnDone: readonly string[] | undefined;
  /** For each shows slot, the output of the last fulfilled answer, or null before any. */
  readonly shown: Map<string, unknown>;
  /** The step that started the instance; Lean's World.act reads it to find the screens that a processing opened. */
  startStep?: number;
  /** The decoded item key of a copy; the map state and the canonical key are in the id. */
  readonly itemKey?: unknown;
  /** For each map state, the encoded keys of its copies, in item order. */
  readonly copyKeys: Map<string, readonly string[]>;
  /**
   * The parameters of each active state that has them, as the edge that entered it filled them; they stay fixed until
   * the state exits.
   */
  readonly held: Map<string, Fields>;
}

/** The instance or copy that takes the transition, and the transition. */
export interface Chosen {
  readonly instance: Instance;
  readonly t: Transition;
}

/** An `after` deadline of an active state, its time fixed when the state was entered. */
export interface Deadline {
  readonly time: number;
  readonly machine: InstanceId;
  readonly state: string;
  readonly name: string;
  /** The step that entered `state`, which armed the deadline. */
  readonly armedBy: number;
}

export const machineOf = (requester: Requester): InstanceId | undefined =>
  requester.kind === "automation" ? undefined : requester.machine;

/**
 * A request with a request line that awaits an answer. A request is `stale` when the sending state has exited or the
 * subscription has ended; a stale request still awaits an answer, but its sender ignores it.
 */
export interface Pending {
  readonly id: LineId;
  readonly activity: Activity;
  readonly requester: Requester;
  readonly input: Json;
  stale: boolean;
  /** The order in which waiting began. A subscription waits again after each answer. */
  turn: number;
}

/**
 * Work that a state began and that awaits the internal queue: the answer to an own-service command that a machine sent,
 * or the opens onDone after the opened screen closes. `serial` is the start order. As in Pending, the work is `stale`
 * when the starting state has exited.
 */
interface Queued {
  readonly serial: number;
  readonly machine: InstanceId;
  readonly state: string;
  stale: boolean;
}

/** Lean's Tie: the deadlines due at one time, or the messages that one line delivers, the first in step `first`. */
export type Tie =
  | { readonly kind: "deadlines"; readonly time: number }
  | { readonly kind: "arrivals"; readonly first: number };

export const sameTie = (a: Tie, b: Tie): boolean =>
  a.kind === "deadlines" ? b.kind === "deadlines" && a.time === b.time : b.kind === "arrivals" && a.first === b.first;

/**
 * Lean's StepOrigin: what began a step. A root step has no cause: an input's first step, or a screen's settling. A
 * caused step continues the message of its cause. A deadline step names the step that armed the deadline and its tie,
 * if any. An arrival step names the tie of its message.
 */
export type StepOrigin =
  | { readonly kind: "root" }
  | { readonly kind: "caused"; readonly cause: number }
  | {
      readonly kind: "deadline";
      readonly armedBy: number;
      readonly tie: Tie | undefined;
    }
  | { readonly kind: "arrival"; readonly tie: Tie };

/** Lean's StepOrigin.cause. */
export const causeOf = (o: StepOrigin): number | undefined => (o.kind === "caused" ? o.cause : undefined);

/** Lean's StepOrigin.tie, of the origin of `step`. */
export function tieOf(step: StepInfo | undefined): Tie | undefined {
  const o = step?.origin;
  return o?.kind === "deadline" || o?.kind === "arrival" ? o.tie : undefined;
}

/**
 * A step of a message. `message` is the message number, inherited from the cause. `command` marks a step that processes
 * an own-service command. `barrier` marks a step that comes after every earlier step of the same message and before
 * every later one.
 */
export interface StepInfo {
  readonly origin: StepOrigin;
  readonly message: number;
  readonly command: boolean;
  readonly barrier: boolean;
}

/** The part of the state that the service persists; a restart keeps it, as in the Raft TLA+ spec's Restart. */
interface Durable {
  readonly records: Records;
  readonly commandAnswers: CommandAnswers;
  /** The ids (idKey) of the events and answers that arrived; one that arrives again is not processed again. */
  readonly deliveries: Set<string>;
  /** Lean's State.createdEntities: the entities that createKey was called for, in call order. */
  readonly createdEntities: string[];
  /** The service whose state this is, which qualifies its createKey values and names its line ids. */
  readonly service: string;
}

/** The part of the state that lives in the service process's memory; a restart drops it. */
interface Process {
  /** Whether service processing has started, which happens at the first input and at each restart. */
  started: boolean;
  /** The machine and screen instances, in creation order. */
  readonly machines: Map<InstanceId, Instance>;
  readonly copies: Map<InstanceId, Instance>;
  /** The open screens, in opening order. */
  readonly stack: InstanceId[];
  /** The deadlines in entry order, which is also the order of the due deadlines. */
  readonly deadlines: Deadline[];
  /** The pending requests, in sending order. */
  readonly pending: Pending[];
  readonly queued: Queued[];
  /** The subscriptions that other services opened, in opening order. */
  readonly subscriptions: Subscriptions<LineId, { readonly query: string; readonly input: unknown }>;
}

/**
 * The state between messages, when the internal queue is empty. The fields follow Lean's State in name and order, with
 * these differences:
 * - Lean's `deadlineCount` and Deadline's `order` have no field: a Deadline is found by identity. `halted` has none:
 *   report throws Halt, and the run stops there.
 * - `lineCounts` is TS only: it counts `lines` per id name.
 * - `machines` and `copies` are maps by id, in the order of Lean's lists.
 * - Records, command answers and deliveries are maps; `subscriptions` is the class that verify also
 *   uses.
 */
export interface State extends Durable, Process {
  now: number;
  /** The entries of the current input's `stepOrder` that the internal queue has not used yet. */
  stepOrder: readonly StepName[];
  serial: number;
  /** The number of the next request to start waiting. */
  turn: number;
  readonly lines: Line[];
  readonly lineCounts: Map<string, number>;
  readonly steps: StepInfo[];
  /** The number of messages begun. Messages are numbered from 1. */
  messageCount: number;
  readonly violations: Violation[];
}

export const newProcess = (): Process => ({
  started: false,
  machines: new Map(),
  copies: new Map(),
  stack: [],
  deadlines: [],
  pending: [],
  queued: [],
  subscriptions: new Subscriptions(idKey),
});

export function newState(st: Service): State {
  const keyed = new Map<string, Map<string, Row>>();
  for (const name of st.entities) if (!st.singles.includes(name)) keyed.set(name, new Map());
  return {
    records: { keyed, singles: new Map() },
    commandAnswers: new Map(),
    deliveries: new Set(),
    createdEntities: [],
    service: st.service,
    ...newProcess(),
    now: 0,
    stepOrder: [],
    serial: 0,
    turn: 0,
    lines: [],
    lineCounts: new Map(),
    steps: [],
    messageCount: 0,
    violations: [],
  };
}

/**
 * A copy of `i` that a run can change apart from `i`; the chart, the ids and the values are shared. Every field is
 * listed, so that a new field fails to compile until it is copied or shared here.
 */
const cloneInstance = (i: Instance): Instance => ({
  chart: i.chart,
  id: i.id,
  context: i.context,
  input: i.input,
  entered: new Map(i.entered),
  lastChildren: new Map(i.lastChildren),
  closed: i.closed,
  awaitingOnDone: i.awaitingOnDone,
  shown: new Map(i.shown),
  ...(i.startStep === undefined ? {} : { startStep: i.startStep }),
  ...("itemKey" in i ? { itemKey: i.itemKey } : {}),
  copyKeys: new Map(i.copyKeys),
  held: new Map(i.held),
});

const cloneInstances = (instances: Map<InstanceId, Instance>): Map<InstanceId, Instance> =>
  new Map([...instances].map(([id, i]) => [id, cloneInstance(i)]));

/**
 * A copy of `s` between messages that a run can continue apart from `s`. Every container is copied, and so is every
 * object with a field that a run sets; objects with readonly fields only (lines, steps, rows, deadlines, values) are
 * shared. Every field is listed, as in cloneInstance.
 */
export function cloneState(s: State): State {
  return {
    records: {
      keyed: new Map([...s.records.keyed].map(([e, rows]) => [e, new Map(rows)])),
      singles: new Map(s.records.singles),
    },
    commandAnswers: new Map(s.commandAnswers),
    deliveries: new Set(s.deliveries),
    createdEntities: [...s.createdEntities],
    service: s.service,
    started: s.started,
    machines: cloneInstances(s.machines),
    copies: cloneInstances(s.copies),
    stack: [...s.stack],
    deadlines: [...s.deadlines],
    pending: s.pending.map((p) => ({ ...p })),
    queued: s.queued.map((q) => ({ ...q })),
    subscriptions: s.subscriptions.clone((v) => v),
    now: s.now,
    stepOrder: s.stepOrder,
    serial: s.serial,
    turn: s.turn,
    lines: [...s.lines],
    lineCounts: new Map(s.lineCounts),
    steps: [...s.steps],
    messageCount: s.messageCount,
    violations: [...s.violations],
  };
}

/** A line before `write` adds the time and, unless the line gives one, the id. */
type UnwrittenLine = LineKind & { readonly id?: LineId };

/** Lean's LineBody.idName: the name that line ids count, as the trace of `service` writes it. */
function idName(service: string, body: LineBody): string {
  switch (body.type) {
    case "command":
    case "query":
    case "subscribe":
      return traceNameOfRef(body.target, service);
    case "event":
      return traceNameOfRef(body.event, service);
    case "operation":
      return operationName(traceNameOfRef(body.screen, service), body.control);
    default:
      return body.type;
  }
}

function lineId(s: State, givenId: LineId | undefined, name: string): LineId {
  return givenId ?? { kind: "own", id: `${name}#${(s.lineCounts.get(name) ?? 0) + 1}` };
}

export function write(s: State, line: UnwrittenLine): LineId {
  const name = idName(s.service, line);
  const id = lineId(s, line.id, name);
  s.lineCounts.set(name, (s.lineCounts.get(name) ?? 0) + 1);
  s.lines.push({ time: s.now, ...line, id });
  return id;
}

/** Lean's State.await: writes the request line and waits for its answer. TS cannot name a function `await`. */
export function awaitAnswer(s: State, line: RequestBody, requester: Requester, activity: Activity): void {
  const id = write(s, { ...line, dir: "out", sender: sender(requester) });
  s.pending.push({ id, activity, requester, input: line.input as Json, stale: false, turn: s.turn });
  s.turn += 1;
}

/** Lean's State.created: the createKey values with their entity, in creation order. */
export function created(s: State): [string, string][] {
  return givenKeys({ owner: s.service, next: [] }, s.createdEntities);
}

function keyCount(s: State, entity: string): number {
  return s.createdEntities.filter((e) => e === entity).length;
}

/** Returns the number of createKey values of each entity, in first-creation order. */
export function keyCounts(s: State): [string, number][] {
  return [...new Set(s.createdEntities)].map((e) => [e, keyCount(s, e)]);
}

/** Lean's State.nextKeys: what createKey returns next for each entity that has a createKey value. */
export function nextKeys(s: State): Keys {
  return {
    owner: s.service,
    next: [...new Set(s.createdEntities)].map((e) => [e, { count: keyCount(s, e) }] as const),
  };
}

export function createKeys(s: State, entities: readonly string[]): void {
  s.createdEntities.push(...entities);
}

export function newMessage(s: State): void {
  s.messageCount += 1;
}

export function newStep(
  s: State,
  origin: StepOrigin,
  { barrier = false, message }: { barrier?: boolean; message?: number } = {},
): number {
  const cause = causeOf(origin);
  const inherited = (cause === undefined ? undefined : s.steps[cause])?.message ?? s.messageCount;
  s.steps.push({ origin, message: message ?? inherited, command: false, barrier });
  return s.steps.length - 1;
}

/** Returns the number of command steps in the cause chain of `step`, including `step`. */
function commandDepth(s: State, step: number): number {
  const info = s.steps[step];
  if (info === undefined) return 0;
  const cause = causeOf(info.origin);
  return (info.command ? 1 : 0) + (cause !== undefined && cause < step ? commandDepth(s, cause) : 0);
}

/**
 * Starts a command step and returns it with the fault of the exceeded limit, if any. `sender` is the definition of the
 * command's sender. The steps of the current message are the last ones.
 */
export function newCommandStep(
  s: State,
  cause: number,
  sender: DefinitionRef,
): { readonly step: number; readonly exceeded: Fault | undefined } {
  const step = newStep(s, { kind: "caused", cause });
  const info = s.steps[step] as StepInfo;
  s.steps[step] = { ...info, command: true };
  const depth = commandDepth(s, step);
  let count = 0;
  for (let k = step; k >= 0 && s.steps[k]?.message === info.message; k -= 1) if (s.steps[k]?.command) count += 1;
  return {
    step,
    exceeded:
      depth > limits.commandDepth
        ? { kind: "Fault.exceededCommandDepth", definition: sender, data: { limit: limits.commandDepth } }
        : count > limits.messageCommands
          ? { kind: "Fault.exceededMessageCommands", definition: sender, data: { limit: limits.messageCommands } }
          : undefined,
  };
}

/** Lean's Service.failedEnsures. */
export function failedEnsures(definition: DefinitionRef, condition: string): Fault {
  return { kind: "Fault.failedEnsures", definition, data: { condition } };
}

/** Lean's Finding, with what only TS reports. */
export type Finding = (Fault | InvalidInput) & Located;

/** Lean's State.halt. */
export function halt(v: Violation): never {
  throw new Halt(v);
}

export class Halt extends Error {
  readonly violation: Violation;
  constructor(violation: Violation) {
    super(violation.kind);
    this.violation = violation;
  }
}

export function report(s: State, v: Finding & { readonly kind: Halting }): never;

export function report(s: State, v: Finding): undefined;

/** Lean's State.report. */
export function report(s: State, v: Finding): undefined {
  if (halts(v.kind)) halt(v);
  s.violations.push(v);
  return undefined;
}

/** Lean's State.reportAll: reports the faults in order up to the first that halts. */
export function reportAll(s: State, faults: readonly (Fault & Located)[]): void {
  for (const f of faults) report(s, f);
}

export function machine(s: State, id: InstanceId): Instance | undefined {
  return s.machines.get(id) ?? s.copies.get(id);
}

/** Lean's Instance.heldAt: the parameters of `state` for its current visit, empty when it has none. */
export function heldAt(instance: Instance, state: string | null): Fields {
  return (state === null ? undefined : instance.held.get(state)) ?? {};
}

/**
 * Returns the scope of the expressions of `instance` at `state`. A copy's expressions also read the owner's context,
 * shown, and input. `held` replaces the parameters of `state`: a transition reads those of its source as the microstep
 * began, since the source has exited.
 */
export function scopeOf(s: State, instance: Instance, state: string | null, held = heldAt(instance, state)): Scope {
  const owner = instance.id.kind === "copy" ? machine(s, ownerId(instance.id)) : undefined;
  if (owner !== undefined)
    return {
      id: instance.id,
      state,
      context: owner.context,
      copy: { key: instance.itemKey, context: instance.context },
      active: { has: (n) => instance.entered.has(n) || owner.entered.has(n) },
      shown: owner.shown,
      input: owner.input,
      held,
      now: s.now,
    };
  return {
    id: instance.id,
    state,
    context: instance.context,
    copy: undefined,
    active: instance.entered,
    shown: instance.shown,
    input: instance.input,
    held,
    now: s.now,
  };
}

/**
 * Lean's State.nthOpen: which of the open instances of the screen of `id`, in opening order, it is, when more
 * than one is open.
 */
export function nthOpen(s: State, id: InstanceId): number | undefined {
  const open = s.stack.filter((r) => chartOf(r) === chartOf(id));
  return open.length > 1 ? open.indexOf(id) : undefined;
}

/**
 * Lean's State.inputFault: the fault of the sender of an input to `target` that the receiver's input schema does not
 * take. Only TS has `error`, the schema's issues.
 */
export function inputFault(r: Run, target: DefinitionRef, sender: string, error: ViolationError | undefined): Finding {
  const fault: Fault = {
    kind: "Fault.inputSchema",
    definition: ref(r.st, sender),
    data: { target },
  };
  return error === undefined ? fault : withExtra(fault, { error });
}

/**
 * Lean's rejectedInput?: the sender's fault when the receiver rejected its input as invalid. Only the receiver
 * parses a message, so the sender wrote an input that the receiver's schema does not take.
 */
export function rejectedInput(
  r: Run,
  target: DefinitionRef,
  sender: string,
  input: unknown,
  answer: Answer,
): Finding | undefined {
  if (answer.result !== "rejected" || answer.rejection.kind !== "invalid-input") return undefined;
  const parsed = r.functions.parse({ kind: "input", definition: target }, input);
  return inputFault(r, target, sender, parsed instanceof Failed || !("error" in parsed) ? undefined : parsed.error);
}

/** Returns the definition that sent the request: the chart of the sending instance, or the automation. */
export function sender(requester: Requester): string {
  return requester.kind === "automation" ? requester.automation : chartOf(requester.machine);
}

/**
 * Returns the depth of the states that a copy enters and exits: the length of the map state's path, or 0 for a
 * non-copy.
 */
export function depth(instance: Instance): number {
  const map = mapOf(instance.id);
  return map === undefined ? 0 : pathOf(instance.chart.tree, map).length;
}

export function copyKeysOf(instance: Instance, map: string): readonly string[] {
  return instance.copyKeys.get(map) ?? [];
}

/** Returns the copies of Lean's copyIds. */
export function copiesOf(s: State, instance: Instance): Instance[] {
  return [...instance.copyKeys].flatMap(([map, keys]) =>
    keys.flatMap((k) => machine(s, copyId(instance.id, map, k)) ?? []),
  );
}

export function documentOrder(s: State, instance: Instance): { holder: Instance; n: string }[] {
  const tree = instance.chart.tree;
  return tree.states.flatMap(({ name: n }) => [
    { holder: instance, n },
    ...copyKeysOf(instance, n).flatMap((k) => {
      const holder = machine(s, copyId(instance.id, n, k));
      return holder === undefined ? [] : descendants(tree, n).map((d) => ({ holder, n: d }));
    }),
  ]);
}

export function removeFromStack(s: State, id: InstanceId): void {
  const index = s.stack.indexOf(id);
  if (index >= 0) s.stack.splice(index, 1);
}

/** Returns the serial of the new Queued. */
export function startQueued(s: State, machine: InstanceId, state: string): number {
  const serial = s.serial;
  s.serial += 1;
  s.queued.push({ serial, machine, state, stale: false });
  return serial;
}

/** Takes the Queued with `serial` and returns whether it is not stale. */
export function takeQueued(s: State, serial: number): boolean {
  const taken = s.queued.find((q) => q.serial === serial);
  if (taken === undefined) return false;
  s.queued.splice(s.queued.indexOf(taken), 1);
  return !taken.stale;
}

/** Records the answer to `request` and returns whether the request is not stale. */
export function answered(s: State, request: Pending): boolean {
  const index = s.pending.indexOf(request);
  if (request.requester.kind === "slot") {
    request.turn = s.turn;
    s.turn += 1;
  } else if (index >= 0) s.pending.splice(index, 1);
  return index >= 0 && !request.stale;
}
