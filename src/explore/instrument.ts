import type { BagOrderDependent } from "../data/bagOrderDependent.generated.ts";
import type { DefinitionRef } from "../data/definitionRef.ts";
import { InternalError } from "../data/internalError.ts";
import type { Activity, StepName } from "../data/step.generated.ts";
import type { Answer } from "../data/trace.generated.ts";
import type { TransitionRef } from "../data/transitionRef.generated.ts";
import type { Undecided } from "../data/undecided.generated.ts";
import type { Fields, Json } from "../data/values.ts";
import type { Located } from "../data/violation.ts";
import type { Schema, Service } from "../service/basic.ts";
import {
  type Access,
  type Assignment,
  type Edge,
  type Functions,
  type Holder,
  holderId,
  type Keys,
  type Scope,
  sorting,
} from "../service/functions.ts";
import { type InstanceId, within } from "../service/instance.ts";
import type { Emit } from "../service/message.ts";
import { type Note, type RegionCheck, type RegionPair, sameStep, type ValueKey, valueName } from "../service/note.ts";
import type { RecordSource } from "../service/records.ts";
import { causeOf, type State, type StepInfo, sameTie, tieOf } from "../service/state.ts";

/**
 * The values that a step reads and writes, each by its valueName. `keyWrites` holds the key sets of entities that a
 * created or deleted record writes.
 */
interface Footprint {
  readonly reads: Set<string>;
  readonly writes: Set<string>;
  readonly keyWrites: Set<string>;
}

/**
 * Returns whether two footprints conflict. Creating or deleting records with different keys commutes, so keyWrites
 * never overlap each other.
 */
function overlaps(a: Footprint, b: Footprint): boolean {
  const some = (values: Set<string>, test: (v: string) => boolean) => [...values].some(test);
  return (
    some(a.writes, (v) => b.reads.has(v) || b.writes.has(v)) ||
    some(b.writes, (v) => a.reads.has(v)) ||
    some(a.keyWrites, (v) => b.reads.has(v)) ||
    some(b.keyWrites, (v) => a.reads.has(v))
  );
}

/** The context fields that one transition part reads and assigns, by valueName. */
interface TransitionAccess {
  readonly reads: Set<string>;
  /** The field of each key. */
  readonly writes: Map<string, string>;
}

function regionFindings(
  chart: DefinitionRef,
  access: (part: number) => TransitionAccess,
  p: RegionPair,
): BagOrderDependent[] {
  const [a, b] = [access(p.first), access(p.second)];
  const { state, firstRef, secondRef } = p;
  const assignRead = (writer: TransitionRef, reader: TransitionRef, field: string): BagOrderDependent => ({
    kind: "BagOrderDependent.assignRead",
    definition: chart,
    data: { state, writer, reader, field },
  });
  return [
    ...[...b.writes].flatMap(([v, field]): BagOrderDependent[] => {
      if (a.writes.has(v))
        return [
          {
            kind: "BagOrderDependent.bothAssign",
            definition: chart,
            data: { state, firstTransition: firstRef, secondTransition: secondRef, field },
          },
        ];
      return a.reads.has(v) ? [assignRead(secondRef, firstRef, field)] : [];
    }),
    ...[...a.writes]
      .filter(([v]) => !b.writes.has(v))
      .flatMap(([v, field]) => (b.reads.has(v) ? [assignRead(firstRef, secondRef, field)] : [])),
  ];
}

/**
 * The access of a step. `reads`, `writes`, and `keyWrites` hold the values that the step and the steps open within it
 * read and wrote.
 */
interface StepAccess extends Footprint {
  readonly name: StepName;
  settledOwner: InstanceId | undefined;
}

/**
 * Lean's startedValue: whether the key is a context field or state of an instance or copy that one of `started` starts,
 * or of its copies.
 */
function startedValue(started: readonly (InstanceId | undefined)[], k: ValueKey): boolean {
  if (k.kind !== "context" && k.kind !== "state") return false;
  return started.some((r) => r !== undefined && within(k.id, r));
}

/** Returns whether always_step_independent proves that the pair commutes. */
function commutes(a: StepAccess, b: StepAccess): boolean {
  return (
    a.settledOwner !== undefined &&
    a.settledOwner === b.settledOwner &&
    (a.name.kind === "always" || b.name.kind === "always")
  );
}

/**
 * Returns whether step `earlier` comes before step `later` through the cause chain or through a barrier of the same
 * message.
 */
export function leadsTo(steps: readonly StepInfo[], earlier: number, later: number): boolean {
  if (later === earlier) return true;
  const first = steps[earlier];
  const last = steps[later];
  if (earlier < later && first?.barrier === true && first.message === last?.message) return true;
  if (last === undefined) return false;
  if (last.barrier && earlier < later && first?.message === last.message) return true;
  const cause = causeOf(last.origin);
  return cause !== undefined && cause < later && leadsTo(steps, earlier, cause);
}

/** Lean's tied: whether steps `i` and `j` are of one tie. */
function tied(steps: readonly StepInfo[], i: number, j: number): boolean {
  const [a, b] = [tieOf(steps[i]), tieOf(steps[j])];
  return a !== undefined && b !== undefined && sameTie(a, b);
}

/** Lean's sameMessage: whether steps `i` and `j` are steps of one message that no tie chose. */
const sameMessage = (steps: readonly StepInfo[], i: number, j: number): boolean =>
  tieOf(steps[i]) === undefined && tieOf(steps[j]) === undefined && steps[i]?.message === steps[j]?.message;

const reportedKey = (v: BagOrderDependent | Undecided): string => JSON.stringify([v.kind, v.definition, v.data]);

/**
 * Lean's Collect: the values each step reads and writes, the context fields each part of the open microstep reads and
 * assigns, the groups of the trace's event lines, and the BagOrderDependent violations. The values come through
 * `read` and `write` from the TS listener, which turns the notes into values because the evaluation cache hears them
 * too.
 */
export class Collect
  implements
    Pick<
      Note,
      | "stepBegins"
      | "stepEnds"
      | "arrivalBegins"
      | "arrivalEnds"
      | "settlesAround"
      | "transitionPart"
      | "microstepEnds"
      | "afterMessageBegins"
      | "afterMessageEnds"
    >
{
  private transition: number | undefined;
  private readonly transitions = new Map<number, TransitionAccess>();
  /** For each step that began and has not ended, outermost first, the instance or copy that it starts. */
  private readonly openSteps: (InstanceId | undefined)[] = [];
  /** The access of each step that began while no step was open, by step number, in the order they began. */
  private readonly steps = new Map<number, StepAccess>();
  /** The access of the step open outermost, which began last of `steps`. */
  private outermost: StepAccess | undefined;
  /** The message whose afterMessage runs, while it runs. */
  private afterMessage: number | undefined;
  /** The access of the step in which a message of a tie arrives, while it is processed (arrivalBegins). */
  private arrival: StepAccess | undefined;
  /** For each message, the values that its afterMessage read: subscription answers and invariants. */
  private readonly afters = new Map<number, Footprint>();
  readonly violations: ((BagOrderDependent | Undecided) & Located)[] = [];
  /** The kind, definition and data of each of `violations`, which Lean's Violation compares. */
  private readonly reported = new Set<string>();

  /**
   * Returns a copy for the next input. Between inputs, no step and no microstep is open, and a closed step's access
   * does not change, so the copy shares them.
   */
  clone(): Collect {
    const open =
      this.transition !== undefined ||
      this.transitions.size > 0 ||
      this.openSteps.length > 0 ||
      this.outermost !== undefined ||
      this.afterMessage !== undefined ||
      this.arrival !== undefined;
    if (open) throw new InternalError("copying a Collect while a step, microstep or afterMessage is open");
    const copy = new Collect();
    for (const [step, access] of this.steps) copy.steps.set(step, access);
    for (const [message, access] of this.afters) copy.afters.set(message, access);
    copy.violations.push(...this.violations);
    for (const key of this.reported) copy.reported.add(key);
    return copy;
  }

  private accessOf(part: number): TransitionAccess {
    return this.transitions.get(part) ?? { reads: new Set(), writes: new Map() };
  }

  /** Lean's addAccess: while a transition part is open, the context fields that `access` hears also go to that part. */
  collecting(scope: Scope, access: Access): Access {
    const part = this.transition;
    if (part === undefined) return access;
    const into = this.accessOf(part);
    this.transitions.set(part, into);
    const key = (holder: Holder, field: string) => valueName({ kind: "context", id: holderId(scope, holder), field });
    return {
      context: (holder, field) => {
        into.reads.add(key(holder, field));
        access.context(holder, field);
      },
      active: (holder, state) => access.active(holder, state),
      assigned: (holder, field) => {
        const k = key(holder, field);
        if (!into.writes.has(k)) into.writes.set(k, field);
        access.assigned(holder, field);
      },
      shown: (slot) => access.shown(slot),
      now: () => access.now(),
    };
  }

  private report(v: BagOrderDependent): void {
    const key = reportedKey(v);
    if (this.reported.has(key)) return;
    this.reported.add(key);
    this.violations.push(v);
  }

  stepBegins(step: number, name: StepName, started: InstanceId | undefined): void {
    if (this.openSteps.length === 0) {
      this.outermost = { name, settledOwner: undefined, reads: new Set(), writes: new Set(), keyWrites: new Set() };
      this.steps.set(step, this.outermost);
    }
    this.openSteps.push(started);
  }

  stepEnds(): void {
    this.openSteps.pop();
    if (this.openSteps.length === 0) this.outermost = undefined;
  }

  arrivalBegins(step: number, name: StepName): void {
    this.arrival = { name, settledOwner: undefined, reads: new Set(), writes: new Set(), keyWrites: new Set() };
    this.steps.set(step, this.arrival);
  }

  arrivalEnds(): void {
    this.arrival = undefined;
  }

  settlesAround(owner: InstanceId): void {
    if (this.outermost !== undefined) this.outermost.settledOwner = owner;
  }

  transitionPart(part: number): void {
    this.transition = part;
  }

  /** Lean's checkRegions. */
  microstepEnds(check: RegionCheck): void {
    for (const found of check.pairs.flatMap((p) => regionFindings(check.chart, (k) => this.accessOf(k), p)))
      this.report(found);
    this.transition = undefined;
    this.transitions.clear();
  }

  afterMessageBegins(message: number): void {
    this.afterMessage = message;
  }

  afterMessageEnds(): void {
    this.afterMessage = undefined;
  }

  /**
   * Lean's stepAccess: the outermost open step, or, while no step is open, the afterMessage that runs, or else the step
   * in which the message of a tie arrived.
   */
  private accessing(): Footprint | undefined {
    if (this.outermost !== undefined) return this.outermost;
    const message = this.afterMessage;
    if (message === undefined) return this.arrival;
    const after = this.afters.get(message) ?? { reads: new Set(), writes: new Set(), keyWrites: new Set() };
    this.afters.set(message, after);
    return after;
  }

  read(name: string): void {
    this.accessing()?.reads.add(name);
  }

  /**
   * Adds a write to the outermost open step, or to the afterMessage that runs. Writes to the instance or copy that an
   * open step starts, or to its copies, never overlap other steps.
   */
  write(key: ValueKey, keyWrite: boolean): void {
    if (startedValue(this.openSteps, key)) return;
    const access = this.accessing();
    if (access !== undefined) (keyWrite ? access.keyWrites : access.writes).add(valueName(key));
  }

  /** Returns the name of each step from step `from` on that began while no step was open, in the order they began. */
  names(from: number): (readonly [number, StepName])[] {
    return [...this.steps].flatMap(([step, access]) => (step < from ? [] : [[step, access.name] as const]));
  }

  /** Lean's involved: the footprint of what step `n` stands for when the search swaps its order. */
  private involved(s: State, n: number, a: StepAccess): Footprint {
    const message = s.steps[n]?.message;
    const tied = tieOf(s.steps[n]) !== undefined;
    const steps: (readonly [number, StepAccess])[] = tied
      ? [...this.steps].filter(([k]) => s.steps[k]?.message === message)
      : [[n, a]];
    const f: Footprint = { reads: new Set(), writes: new Set(), keyWrites: new Set() };
    const after = tied && message !== undefined ? this.afters.get(message) : undefined;
    for (const x of [...(after === undefined ? [] : [after]), ...steps.map(([, x]) => x)]) {
      for (const v of x.reads) f.reads.add(v);
      for (const v of x.writes) f.writes.add(v);
      for (const v of x.keyWrites) f.keyWrites.add(v);
    }
    return f;
  }

  /** Returns Lean's candidates of a run that did not halt, of the steps from step `from` on. */
  candidates(s: State, from: number): (readonly [number, number])[] {
    const footprints = new Map([...this.steps].map(([n, a]) => [n, this.involved(s, n, a)] as const));
    const tagged = [...this.steps].filter(([step]) => step >= from);
    return tagged.flatMap(([i, a], n) =>
      tagged
        .slice(n + 1)
        .filter(
          ([j, b]) =>
            (tied(s.steps, i, j) || sameMessage(s.steps, i, j)) &&
            overlaps(footprints.get(i) as Footprint, footprints.get(j) as Footprint) &&
            !commutes(a, b) &&
            !sameStep(a.name, b.name) &&
            !leadsTo(s.steps, i, j),
        )
        .map(([j]) => [i, j] as const),
    );
  }
}

/** Lean's `instrument`, which returns the same values as `sorting(st, fs)` and collects what each call accesses. */
export class InstrumentedFunctions implements Functions {
  readonly st: Service;
  private readonly fs: Functions;
  private readonly c: Collect;

  constructor(st: Service, fs: Functions, c: Collect) {
    this.st = st;
    this.fs = sorting(st, fs);
    this.c = c;
  }

  parse(schema: Schema, value: unknown) {
    return this.fs.parse(schema, value);
  }
  unordered(schema: Schema, value: unknown): unknown {
    return this.fs.unordered(schema, value);
  }
  decode(schema: Schema, value: Json) {
    return this.fs.decode(schema, value);
  }
  binding(command: string, binding: string, input: Fields, records: RecordSource, now: number) {
    return this.fs.binding(command, binding, input, records, now);
  }
  requirement(command: string, condition: string, input: Fields, records: RecordSource, now: number) {
    return this.fs.requirement(command, condition, input, records, now);
  }
  inputRequirement(target: DefinitionRef, condition: string, input: Fields) {
    return this.fs.inputRequirement(target, condition, input);
  }
  decide(command: string, input: Fields, records: RecordSource, now: number) {
    return this.fs.decide(command, input, records, now);
  }
  ensures(command: string, input: Fields, before: RecordSource, after: RecordSource, now: number) {
    return this.fs.ensures(command, input, before, after, now);
  }
  queryEnsures(query: string, input: Fields, output: Fields, records: RecordSource) {
    return this.fs.queryEnsures(query, input, output, records);
  }
  resultEnsures(target: DefinitionRef, condition: string, input: Fields, output: unknown, events: readonly Emit[]) {
    return this.fs.resultEnsures(target, condition, input, output, events);
  }
  invariant(entity: string, record: Fields) {
    return this.fs.invariant(entity, record);
  }
  serviceInvariant(records: RecordSource) {
    return this.fs.serviceInvariant(records);
  }
  chartInvariant(scope: Scope, records: RecordSource, access: Access) {
    return this.fs.chartInvariant(scope, records, this.c.collecting(scope, access));
  }
  resolve(query: string, input: Fields, records: RecordSource, now: number) {
    return this.fs.resolve(query, input, records, now);
  }
  automationBinding(automation: string, binding: string, payload: Fields, records: RecordSource, now: number) {
    return this.fs.automationBinding(automation, binding, payload, records, now);
  }
  automationGuard(automation: string, condition: string, payload: Fields, records: RecordSource, now: number) {
    return this.fs.automationGuard(automation, condition, payload, records, now);
  }
  react(automation: string, payload: Fields, records: RecordSource, now: number, keys: Keys) {
    return this.fs.react(automation, payload, records, now, keys);
  }
  comparable(query: string, answer: Answer): unknown {
    return this.fs.comparable(query, answer);
  }
  initialContext(machine: string, input: Fields) {
    return this.fs.initialContext(machine, input);
  }
  guard(
    scope: Scope,
    records: RecordSource,
    transition: TransitionRef,
    condition: string,
    extra: Fields,
    access: Access,
  ) {
    return this.fs.guard(scope, records, transition, condition, extra, this.c.collecting(scope, access));
  }
  assign(scope: Scope, records: RecordSource, assignment: Assignment, extra: Fields, keys: Keys, access: Access) {
    return this.fs.assign(scope, records, assignment, extra, keys, this.c.collecting(scope, access));
  }
  input(scope: Scope, records: RecordSource, activity: Activity, keys: Keys, access: Access) {
    return this.fs.input(scope, records, activity, keys, this.c.collecting(scope, access));
  }
  held(scope: Scope, records: RecordSource, state: string, edge: Edge, extra: Fields, access: Access) {
    return this.fs.held(scope, records, state, edge, extra, this.c.collecting(scope, access));
  }
  deadlineAt(scope: Scope, records: RecordSource, name: string, access: Access) {
    return this.fs.deadlineAt(scope, records, name, this.c.collecting(scope, access));
  }
  offers(scope: Scope, records: RecordSource, control: string, access: Access) {
    return this.fs.offers(scope, records, control, this.c.collecting(scope, access));
  }
  showInput(scope: Scope, records: RecordSource, activity: Activity, access: Access) {
    return this.fs.showInput(scope, records, activity, this.c.collecting(scope, access));
  }
  items(scope: Scope, records: RecordSource, access: Access) {
    return this.fs.items(scope, records, this.c.collecting(scope, access));
  }
  defaults(schema: Schema) {
    return this.fs.defaults(schema);
  }
  close(scope: Scope, records: RecordSource, access: Access) {
    return this.fs.close(scope, records, this.c.collecting(scope, access));
  }
  closeEnsures(screen: string, input: Fields, output: Fields) {
    return this.fs.closeEnsures(screen, input, output);
  }
}
