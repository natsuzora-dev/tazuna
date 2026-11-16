import type { StepName, Who } from "../data/choiceDependent.generated.ts";
import type { DefinitionRef } from "../data/definitionRef.ts";
import type { Fault } from "../data/fault.generated.ts";
import type { InvalidInput } from "../data/invalidInput.generated.ts";
import { Subscriptions } from "../data/subscriptions.ts";
import type { Answer, DeadlineId, TraceLine } from "../data/trace.generated.ts";
import type { UntimedTraceLine } from "../data/trace.ts";
import { type Fields, plain } from "../data/values.ts";
import type { Located, Location, Violation } from "../data/violation.ts";
import { descendants, pathOf } from "../syntax/tree.ts";
import type { Activity, Chart, Transition } from "./chart/basic.ts";
import { type Access, type Functions, type Holder, holderResource, type Scope } from "./functions.ts";
import { limits } from "./limits.ts";
import { type Emit, type Halting, halts } from "./message.ts";
import type { Note } from "./note.ts";
import { ref, type Service } from "./service/basic.ts";
import type { CommandAnswers, EventDeliveries } from "./service/idempotency.ts";
import type { Records, Row } from "./service/records.ts";

/**
 * TS only: the evaluation cache, which hears reads and writes through the note. An evaluation of `part` of the instance
 * `resource` (its always transitions, or the items of a map state) is fresh while none of the names it read has been
 * written since.
 */
export interface Evaluations {
  /**
   * Returns whether the evaluation is fresh; when it is, the evaluations being tracked and the note hear its reads
   * again.
   */
  replayIfFresh(resource: string, part: string): boolean;
  /** Returns the names that `f` reads, in first-read order. */
  track(f: () => void): string[];
  /**
   * Stores an evaluation whose `reads` are heard again while it is fresh; a write to any of `watched` makes it stale.
   */
  remember(resource: string, part: string, reads: readonly string[], watched: readonly string[]): void;
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
    this.r.note.readContext(holderResource(this.scope, holder), field);
  }

  active(holder: Holder, state: string): void {
    this.r.note.readStates([[holderResource(this.scope, holder), state]]);
  }

  assigned(holder: Holder, field: string): void {
    this.r.note.wroteContext(holderResource(this.scope, holder), field);
  }

  shown(slot: string): void {
    this.r.note.readShown(holderResource(this.scope, "owner"), slot);
  }

  now(): void {
    this.r.note.readNow();
  }
}

/** Runs `work` and tells the instrumentation that step `step` begins and ends. */
export function inStep(
  r: Run,
  step: number,
  name: StepName,
  startedResource: string | undefined,
  work: () => void,
): void {
  r.note.stepBegins(step, name, startedResource);
  try {
    work();
  } finally {
    r.note.stepEnds();
  }
}

export function copyName(owner: string, map: string, key: string): string {
  return `${owner}@${map}[${key}]`;
}

/**
 * An instance of a machine or screen, or a copy of a map state. A machine, or a screen that no other screen opens, has
 * one instance per definition; `opens` creates an instance each time it opens a screen. `resource` is the read and
 * write name of the instance or copy: resource.field for a context field, resource@s for being in state s, and
 * resource:slot for a shows slot.
 */
export interface Instance {
  readonly chart: Chart;
  readonly resource: string;
  context: Fields;
  readonly input: Fields;
  /** The active states and their entry times, in entry order. */
  readonly entered: Map<string, Temporal.Instant>;
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
  /** The instance that opened this screen; `parent` is its resource. */
  readonly opener?: {
    readonly parent: string;
    readonly state: string;
    readonly key: string;
    readonly modal: boolean;
  };
  /**
   * The map state of this copy; `owner` is the owner instance's resource, and `encodedKey` is canonicalJson of `key`.
   */
  readonly copyOf?: {
    readonly owner: string;
    readonly map: string;
    readonly key: unknown;
    readonly encodedKey: string;
  };
  /** For each map state, the encoded keys of its copies, in item order. */
  readonly copyKeys: Map<string, readonly string[]>;
  /** Lean's State.who of the instance or copy, kept so that notes do not build it again. */
  readonly who: Who;
}

/** The instance or copy that takes the transition, and the transition. */
export interface Chosen {
  readonly instance: Instance;
  readonly t: Transition;
}

/** An `after` deadline of an active state. An `at` deadline (`fromAt`) has no `time` until it is computed. */
export interface Deadline {
  time: Temporal.Instant | undefined;
  readonly fromAt: boolean;
  readonly machine: string;
  readonly state: string;
  readonly name: string;
}

export const deadlineId = (deadline: Deadline): DeadlineId => ({
  instance: deadline.machine,
  state: deadline.state,
  name: deadline.name,
});

/**
 * The sender of a request. A `state` requester is machine `machine`, which sent the request on entering `state`. A
 * `slot` requester is screen `machine`, which subscribed to the query of shows slot `slot`; answers keep coming until
 * the subscription ends.
 */
export type Requester =
  | { readonly kind: "state"; readonly machine: string; readonly state: string }
  | { readonly kind: "slot"; readonly machine: string; readonly slot: string }
  | { readonly kind: "automation"; readonly automation: string };

export const machineOf = (requester: Requester): string | undefined =>
  requester.kind === "automation" ? undefined : requester.machine;

/**
 * A request with a request line that awaits an answer. A request is `stale` when the sending state has exited or the
 * subscription has ended; a stale request still awaits an answer, but its sender ignores it.
 */
export interface Pending {
  readonly id: string;
  readonly activity: Activity;
  readonly requester: Requester;
  /** The JSON of the encoded input. */
  readonly input: string;
  /** The decoded input. */
  readonly value: Fields;
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
  readonly machine: string;
  readonly state: string;
  stale: boolean;
}

/**
 * A step of a message. `cause` is the step that caused this one, undefined for input and deadline steps. `message` is
 * the message number, inherited from the cause. `command` marks a step that processes an own-service command. `barrier`
 * marks a step that comes after every earlier step of the same message and before every later one. `nested` marks a
 * step that began while its cause was running (a copy start), so it ends before its cause does.
 */
export interface StepInfo {
  readonly cause: number | undefined;
  readonly message: number;
  readonly command: boolean;
  readonly barrier: boolean;
  readonly nested: boolean;
}

/** A recorded acceptance of an external command and the result events received so far, with decoded values. */
export interface Accepted {
  readonly id: string;
  readonly activity: Activity;
  readonly input: Fields;
  readonly output: unknown;
  readonly events: Emit[];
}

/**
 * The state between messages, when the internal queue is empty. The fields follow Lean's State in name and order, with
 * these differences:
 * - Lean's `deadlineCount` and Deadline's `order` have no field: a Deadline is found by identity. `halted` has none:
 *   report throws Halt, and the run stops there.
 * - `lineCounts` is TS only: it counts `lines` per id name.
 * - `machines` and `copies` are maps by resource, in the order of Lean's lists.
 * - Records, command answers, event deliveries and results are maps; `subscriptions` is the class that verify also
 *   uses.
 */
export interface State {
  now: Temporal.Instant;
  /** Whether service processing has started, which happens at the first input and at each restart. */
  started: boolean;
  readonly records: Records;
  readonly commandAnswers: CommandAnswers;
  readonly eventDeliveries: EventDeliveries;
  /** The machine and screen instances, in creation order. */
  readonly machines: Map<string, Instance>;
  readonly copies: Map<string, Instance>;
  /** The resources of the open screens, in opening order. */
  readonly stack: string[];
  /** The deadlines in entry order, which is also the order of the due deadlines. */
  readonly deadlines: Deadline[];
  /** The current input's `deadlineOrder`, which its `in` line carries. */
  inputDeadlineOrder: readonly DeadlineId[];
  /** The entries of the current input's `deadlineOrder` that no tie has used yet. */
  deadlineOrder: readonly DeadlineId[];
  /** The entries of the current input's `stepOrder` that the internal queue has not used yet. */
  stepOrder: readonly StepName[];
  /** The pending requests, in sending order. */
  readonly pending: Pending[];
  readonly queued: Queued[];
  serial: number;
  /** The number of the next request to start waiting. */
  turn: number;
  readonly lines: TraceLine[];
  readonly lineCounts: Map<string, number>;
  readonly steps: StepInfo[];
  /** The number of messages begun. Messages are numbered from 1. */
  messageCount: number;
  /** The createKey values and the names of their entities, in creation order. */
  readonly created: (readonly [string, string])[];
  /** The subscriptions that other services opened, in opening order. */
  subscriptions: Subscriptions<{ readonly query: string; readonly input: unknown }>;
  readonly results: Map<string, Accepted>;
  /** For each handle of a processed mock input, the request that the latest such input answered and the answer. */
  readonly mocks: Map<string, { readonly request: Pending; readonly answer: Answer }>;
  readonly violations: Violation[];
}

export function newState(st: Service): State {
  const keyed = new Map<string, Map<string, Row>>();
  for (const name of st.entities) if (!st.singles.includes(name)) keyed.set(name, new Map());
  return {
    now: Temporal.Instant.fromEpochMilliseconds(0),
    started: false,
    records: { keyed, singles: new Map() },
    commandAnswers: new Map(),
    eventDeliveries: new Map(),
    machines: new Map(),
    copies: new Map(),
    stack: [],
    deadlines: [],
    inputDeadlineOrder: [],
    deadlineOrder: [],
    stepOrder: [],
    pending: [],
    queued: [],
    serial: 0,
    turn: 0,
    lines: [],
    lineCounts: new Map(),
    steps: [],
    messageCount: 0,
    created: [],
    subscriptions: new Subscriptions(),
    results: new Map(),
    mocks: new Map(),
    violations: [],
  };
}

/** A trace line before `write` adds the time and, unless the line gives one, the id. */
type UnwrittenLine = UntimedTraceLine extends infer L
  ? L extends UntimedTraceLine
    ? Omit<L, "id"> & { readonly id?: string }
    : never
  : never;

export function lineId(s: State, givenId: string | undefined, name: string): string {
  return givenId ?? `${name}#${(s.lineCounts.get(name) ?? 0) + 1}`;
}

export function write(s: State, line: UnwrittenLine): string {
  const name = "name" in line ? line.name : line.type;
  const id = lineId(s, line.id, name);
  s.lineCounts.set(name, (s.lineCounts.get(name) ?? 0) + 1);
  s.lines.push({ time: s.now.toString(), ...line, id });
  return id;
}

/** Writes the `in` line of the current input, with the input's `deadlineOrder`. */
export function writeInput(s: State, line: UnwrittenLine): string {
  return write(s, s.inputDeadlineOrder.length === 0 ? line : { ...line, deadlineOrder: [...s.inputDeadlineOrder] });
}

/** Lean's State.await: writes the request line and waits for its answer. TS cannot name a function `await`. */
export function awaitAnswer(
  s: State,
  line: Extract<UnwrittenLine, { readonly type: "command" | "query" | "subscribe" }>,
  requester: Requester,
  activity: Activity,
  value: Fields,
): void {
  const id = write(s, line);
  s.pending.push({ id, activity, requester, input: JSON.stringify(line.input), value, stale: false, turn: s.turn });
  s.turn += 1;
}

function keyCount(s: State, entity: string): number {
  return s.created.filter(([e]) => e === entity).length;
}

/** Returns the number of createKey values of each entity, in first-creation order. */
export function keyCounts(s: State): [string, number][] {
  return [...new Set(s.created.map(([e]) => e))].map((e) => [e, keyCount(s, e)]);
}

/** Returns whether `value` has the form of a createKey value of entity `entity`, which createKey numbers from 1. */
export function isKeyOf(entity: string, value: string): boolean {
  const n = Number(value.slice(entity.length + 1));
  return Number.isSafeInteger(n) && n > 0 && value === `${entity}-${n}`;
}

function createKey(s: State, entity: string): void {
  s.created.push([entity, `${entity}-${keyCount(s, entity) + 1}`]);
}

export function createKeys(s: State, entities: readonly string[]): void {
  for (const entity of entities) createKey(s, entity);
}

export function newMessage(s: State): void {
  s.messageCount += 1;
}

export function newStep(s: State, cause: number | undefined, { barrier = false, nested = false } = {}): number {
  const message = (cause === undefined ? undefined : s.steps[cause])?.message ?? s.messageCount;
  s.steps.push({ cause, message, command: false, barrier, nested });
  return s.steps.length - 1;
}

/** Returns the number of command steps in the cause chain of `step`, including `step`. */
function commandDepth(s: State, step: number): number {
  const info = s.steps[step];
  if (info === undefined) return 0;
  const { cause, command } = info;
  return (command ? 1 : 0) + (cause !== undefined && cause < step ? commandDepth(s, cause) : 0);
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
  const step = newStep(s, cause);
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

/** Returns the instance or copy whose resource is `resource`. */
export function machine(s: State, resource: string): Instance | undefined {
  return s.machines.get(resource) ?? s.copies.get(resource);
}

/**
 * Returns the scope of the expressions of `instance`. A copy's expressions also read the owner's context, shown, and
 * input.
 */
export function scopeOf(s: State, instance: Instance, state: string | null): Scope {
  const copy = instance.copyOf;
  const owner = copy === undefined ? undefined : machine(s, copy.owner);
  if (copy !== undefined && owner !== undefined)
    return {
      machine: instance.chart.name,
      resource: instance.resource,
      owner: owner.resource,
      state,
      context: owner.context,
      copy: { map: copy.map, key: copy.key, context: instance.context },
      active: { has: (n) => instance.entered.has(n) || owner.entered.has(n) },
      shown: owner.shown,
      input: owner.input,
      now: s.now,
    };
  return {
    machine: instance.chart.name,
    resource: instance.resource,
    owner: instance.resource,
    state,
    context: instance.context,
    copy: undefined,
    active: instance.entered,
    shown: instance.shown,
    input: instance.input,
    now: s.now,
  };
}

export function chartName(s: State, name: string): string {
  return machine(s, name)?.chart.name ?? name;
}

/** Returns the instance or automation that sent the request. */
export function sender(requester: Requester): string {
  return requester.kind === "automation" ? requester.automation : requester.machine;
}

/** Returns the chart or automation that a mock's `sender` names. */
export function senderOf(s: State, requester: Requester): string {
  return requester.kind === "automation" ? requester.automation : chartName(s, requester.machine);
}

/**
 * Returns the depth of the states that a copy enters and exits: the length of the map state's path, or 0 for a
 * non-copy.
 */
export function depth(instance: Instance): number {
  const copy = instance.copyOf;
  return copy === undefined ? 0 : pathOf(instance.chart.tree, copy.map).length;
}

export function copyKeysOf(instance: Instance, map: string): readonly string[] {
  return instance.copyKeys.get(map) ?? [];
}

/** Returns the copies of Lean's copyResources. */
export function copiesOf(s: State, instance: Instance): Instance[] {
  return [...instance.copyKeys].flatMap(([map, keys]) =>
    keys.flatMap((k) => machine(s, copyName(instance.resource, map, k)) ?? []),
  );
}

export function documentOrder(s: State, instance: Instance): { holder: Instance; n: string }[] {
  const tree = instance.chart.tree;
  return tree.states.flatMap(({ name: n }) => [
    { holder: instance, n },
    ...copyKeysOf(instance, n).flatMap((k) => {
      const holder = machine(s, copyName(instance.resource, n, k));
      return holder === undefined ? [] : descendants(tree, n).map((d) => ({ holder, n: d }));
    }),
  ]);
}

export function instanceWho(instance: Pick<Instance, "chart" | "copyOf">, st: Service): Who {
  const copy = instance.copyOf;
  return {
    chart: ref(st, instance.chart.name),
    copy: copy === undefined ? null : { map: copy.map, itemKey: plain(copy.key) },
  };
}

/** Returns the who of `resource`. Each instance and copy keeps its instanceWho. */
export function who(s: State, st: Service, resource: string): Who {
  return machine(s, resource)?.who ?? { chart: ref(st, resource), copy: null };
}

export function ownerOf(s: State, resource: string): string {
  return machine(s, resource)?.copyOf?.owner ?? resource;
}

export function* running(s: State): Generator<Instance> {
  for (const instance of s.machines.values()) yield* [instance, ...copiesOf(s, instance)];
}

export function removeFromStack(s: State, resource: string): void {
  const index = s.stack.indexOf(resource);
  if (index >= 0) s.stack.splice(index, 1);
}

/** Returns the serial of the new Queued. */
export function startQueued(s: State, machine: string, state: string): number {
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

/** Returns the activities of the requests that await answers, except subscriptions, which answer until they end. */
export function awaitedActivities(s: State): Activity[] {
  return s.pending.filter((p) => p.requester.kind !== "slot").map((p) => p.activity);
}
