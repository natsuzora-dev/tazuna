import type { StepName } from "../data/choiceDependent.generated.ts";
import type { DefinitionRef } from "../data/definitionRef.ts";
import type { OrderDependent } from "../data/orderDependent.generated.ts";
import type { Answer } from "../data/trace.generated.ts";
import type { TransitionRef } from "../data/transitionRef.ts";
import { canonicalJson, type Fields, plain } from "../data/values.ts";
import { type Located, withExtra } from "../data/violation.ts";
import {
  type Access,
  type Assignment,
  Failed,
  type Functions,
  type Holder,
  holderResource,
  type Scope,
} from "../semantics/functions.ts";
import type { Emit } from "../semantics/message.ts";
import type { Note, RegionCheck, RegionPair } from "../semantics/note.ts";
import { ref, type Schema, type Service } from "../semantics/service/basic.ts";
import { normalizeOutput } from "../semantics/service/query.ts";
import type { RecordSource } from "../semantics/service/records.ts";
import type { StepInfo } from "../semantics/state.ts";
import { type Causes, leadsTo } from "./trace.ts";

/** Lean's contextKey: the name of a context field, unique across the kinds of value, as recordPartName names parts. */
export const contextKey = (resource: string, field: string): string => `context:${resource}.${field}`;

export const shownKey = (resource: string, slot: string): string => `shown:${resource}:${slot}`;

/**
 * The values that a step reads and writes, each by its name. `keyWrites` holds the key sets of entities that a created
 * or deleted record writes.
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

/** The context fields that one transition part reads and assigns, keyed by their resource and field. */
interface TransitionAccess {
  readonly reads: Set<string>;
  /** The field of each key. */
  readonly writes: Map<string, string>;
}

function regionFindings(
  chart: DefinitionRef,
  access: (part: number) => TransitionAccess,
  p: RegionPair,
): OrderDependent[] {
  const [a, b] = [access(p.first), access(p.second)];
  const { state, firstRef, secondRef } = p;
  const assignRead = (writer: TransitionRef, reader: TransitionRef, field: string): OrderDependent => ({
    kind: "OrderDependent.assignRead",
    definition: chart,
    data: { state, writer, reader, field },
  });
  return [
    ...[...b.writes].flatMap(([v, field]): OrderDependent[] => {
      if (a.writes.has(v))
        return [
          {
            kind: "OrderDependent.bothAssign",
            definition: chart,
            data: { state, first: firstRef, second: secondRef, field },
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
  settledOwner: string | undefined;
}

/** Returns whether always_step_independent proves that the pair commutes. */
function commutes(a: StepAccess, b: StepAccess): boolean {
  return (
    a.settledOwner !== undefined &&
    a.settledOwner === b.settledOwner &&
    (a.name.kind === "always" || b.name.kind === "always")
  );
}

const reportedKey = (v: OrderDependent): string => JSON.stringify([v.kind, v.definition, v.data]);

/**
 * Lean's Collect: the values each step reads and writes, the context fields each part of the open microstep reads and
 * assigns, the causes that order the trace's event lines, and the OrderDependent violations. The values come through
 * `read` and `write` from the TS listener, which turns the notes into values because the evaluation cache hears them
 * too.
 */
export class Collect
  implements
    Pick<Note, "events" | "deadline" | "stepBegins" | "stepEnds" | "settlesAround" | "transitionPart" | "microstepEnds">
{
  /** The queries already reported for order-dependent output. */
  private readonly reportedOrder = new Set<string>();
  private transition: number | undefined;
  private readonly transitions = new Map<number, TransitionAccess>();
  /** For each step that began and has not ended, outermost first, the instance or copy that it starts. */
  private readonly openSteps: (string | undefined)[] = [];
  /** The access of each step that began while no step was open, by step number, in the order they began. */
  private readonly steps = new Map<number, StepAccess>();
  /** The access of the step open outermost, which began last of `steps`. */
  private outermost: StepAccess | undefined;
  readonly violations: (OrderDependent & Located)[] = [];
  /** The kind, definition and data of each of `violations`, which Lean's Violation compares. */
  private readonly reported = new Set<string>();
  readonly causes: Causes = { events: [], deadlines: [] };

  /**
   * Returns a copy for the next input. Between inputs, no step and no microstep is open, and a closed step's access
   * does not change, so the copy shares them.
   */
  clone(): Collect {
    const copy = new Collect();
    for (const name of this.reportedOrder) copy.reportedOrder.add(name);
    for (const [step, access] of this.steps) copy.steps.set(step, access);
    copy.violations.push(...this.violations);
    for (const key of this.reported) copy.reported.add(key);
    copy.causes.events.push(...this.causes.events);
    copy.causes.deadlines.push(...this.causes.deadlines);
    return copy;
  }

  hasReportedOrder(name: string): boolean {
    return this.reportedOrder.has(name);
  }

  reportOrder(name: string, v: OrderDependent & Located): void {
    this.reportedOrder.add(name);
    this.reported.add(reportedKey(v));
    this.violations.push(v);
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
    const key = (holder: Holder, field: string) => JSON.stringify([holderResource(scope, holder), field]);
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

  private report(v: OrderDependent): void {
    const key = reportedKey(v);
    if (this.reported.has(key)) return;
    this.reported.add(key);
    this.violations.push(v);
  }

  events(step: number, start: number, count: number): void {
    this.causes.events.push([step, start, count]);
  }

  deadline(message: number, time: Temporal.Instant): void {
    this.causes.deadlines.push([message, time]);
  }

  stepBegins(step: number, name: StepName, startedResource: string | undefined): void {
    if (this.openSteps.length === 0) {
      this.outermost = { name, settledOwner: undefined, reads: new Set(), writes: new Set(), keyWrites: new Set() };
      this.steps.set(step, this.outermost);
    }
    this.openSteps.push(startedResource);
  }

  stepEnds(): void {
    this.openSteps.pop();
    if (this.openSteps.length === 0) this.outermost = undefined;
  }

  settlesAround(owner: string): void {
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

  read(key: string): void {
    this.outermost?.reads.add(key);
  }

  /**
   * Adds a write to the outermost open step. Writes to the instance or copy that an open step starts, or to its copies,
   * never overlap other steps.
   */
  write(key: string, keyWrite: boolean): void {
    const access = this.outermost;
    const started = (resource: string | undefined) =>
      resource !== undefined &&
      (key.startsWith(`context:${resource}.`) ||
        key.startsWith(`context:${resource}@`) ||
        key.startsWith(`state:${resource}@`));
    if (access === undefined || this.openSteps.some(started)) return;
    (keyWrite ? access.keyWrites : access.writes).add(key);
  }

  /** Returns the name of each step from step `from` on that began while no step was open, in the order they began. */
  names(from: number): (readonly [number, StepName])[] {
    return [...this.steps].flatMap(([step, access]) => (step < from ? [] : [[step, access.name] as const]));
  }

  /** Returns Lean's candidates of a run that did not halt, of the steps from step `from` on. */
  candidates(steps: readonly StepInfo[], from: number): (readonly [number, number])[] {
    const tagged = [...this.steps].filter(([step]) => step >= from);
    return tagged.flatMap(([i, a], n) =>
      tagged
        .slice(n + 1)
        .filter(
          ([j, b]) =>
            steps[i]?.message === steps[j]?.message &&
            overlaps(a, b) &&
            !commutes(a, b) &&
            canonicalJson(a.name) !== canonicalJson(b.name) &&
            !leadsTo(steps, i, j),
        )
        .map(([j]) => [i, j] as const),
    );
  }
}

/**
 * Lean's InstrumentFunctions without lastReads and lastAccess, which the TS run tells as it reads. `reversed` returns
 * the query output with records in reverse key order.
 */
export interface InstrumentFunctions {
  reversed(query: string, input: Fields, records: RecordSource, now: Temporal.Instant): unknown;
}

/** Lean's `instrument`, which returns the same values as `fs`. */
export class InstrumentedFunctions implements Functions {
  readonly st: Service;
  private readonly fs: Functions;
  private readonly ifs: InstrumentFunctions;
  private readonly c: Collect;

  constructor(st: Service, fs: Functions, ifs: InstrumentFunctions, c: Collect) {
    this.st = st;
    this.fs = fs;
    this.ifs = ifs;
    this.c = c;
  }

  /**
   * Runs query `name` again with records in reverse key order and reports OrderDependent.reversedRecords when its
   * comparable output changes, OrderDependent.reversedOutputSchema when the output fails the schema, or
   * OrderDependent.reversedException when an Issue stops that run, the check of its output or its comparable value. At
   * most once per query. An Issue in the comparable value of `output` is no order dependence and reports nothing.
   */
  private orderAudit(name: string, input: Fields, records: RecordSource, now: Temporal.Instant, output: unknown) {
    if (this.c.hasReportedOrder(name)) return;
    const definition = ref(this.st, name);
    const report = (found: OrderDependent & Located) => this.c.reportOrder(name, found);
    const exception = ({ error }: Failed) =>
      report(withExtra({ kind: "OrderDependent.reversedException", definition, data: {} }, { error }));
    const reversed = this.ifs.reversed(name, input, records, now);
    if (reversed instanceof Failed) return exception(reversed);
    const checked = normalizeOutput(this.st, this.fs, name, reversed);
    if (checked instanceof Failed) return exception(checked);
    if ("error" in checked)
      return report(
        withExtra({ kind: "OrderDependent.reversedOutputSchema", definition, data: {} }, { error: checked.error }),
      );
    const original = this.fs.comparable(name, { result: "fulfilled", output });
    if (original instanceof Failed) return;
    const reordered = this.fs.comparable(name, { result: "fulfilled", output: checked.encoded });
    if (reordered instanceof Failed) return exception(reordered);
    if (canonicalJson(original) === canonicalJson(reordered)) return;
    report({
      kind: "OrderDependent.reversedRecords",
      definition,
      data: { original: plain(output), reversed: plain(checked.encoded) },
    });
  }

  parse(schema: Schema, value: unknown) {
    return this.fs.parse(schema, value);
  }
  canonical(schema: Schema, value: unknown): unknown {
    return this.fs.canonical(schema, value);
  }
  normalize(schema: Schema, value: unknown) {
    return this.fs.normalize(schema, value);
  }
  binding(command: string, binding: string, input: Fields, records: RecordSource, now: Temporal.Instant) {
    return this.fs.binding(command, binding, input, records, now);
  }
  requirement(command: string, condition: string, input: Fields, records: RecordSource, now: Temporal.Instant) {
    return this.fs.requirement(command, condition, input, records, now);
  }
  inputRequirement(target: string, condition: string, input: Fields) {
    return this.fs.inputRequirement(target, condition, input);
  }
  decide(command: string, input: Fields, records: RecordSource, now: Temporal.Instant) {
    return this.fs.decide(command, input, records, now);
  }
  ensures(command: string, input: Fields, before: RecordSource, after: RecordSource, now: Temporal.Instant) {
    return this.fs.ensures(command, input, before, after, now);
  }
  queryEnsures(query: string, input: Fields, output: Fields, records: RecordSource) {
    return this.fs.queryEnsures(query, input, output, records);
  }
  resultEnsures(target: string, input: Fields, output: unknown, events: readonly Emit[]) {
    return this.fs.resultEnsures(target, input, output, events);
  }
  invariant(entity: string, record: Fields) {
    return this.fs.invariant(entity, record);
  }
  serviceInvariant(records: RecordSource) {
    return this.fs.serviceInvariant(records);
  }
  chartInvariant(scope: Scope, records: RecordSource, access: Access) {
    return this.fs.chartInvariant(scope, records, access);
  }
  /** Lean's resolveCollect. */
  resolve(query: string, input: Fields, records: RecordSource, now: Temporal.Instant): unknown {
    const resolved = this.fs.resolve(query, input, records, now);
    if (resolved instanceof Failed) return resolved;
    const checked = normalizeOutput(this.st, this.fs, query, resolved);
    if (!(checked instanceof Failed) && !("error" in checked))
      this.orderAudit(query, input, records, now, checked.encoded);
    return resolved;
  }
  react(
    automation: string,
    payload: Fields,
    records: RecordSource,
    now: Temporal.Instant,
    keys: readonly (readonly [string, number])[],
  ) {
    return this.fs.react(automation, payload, records, now, keys);
  }
  comparable(query: string, answer: Answer): unknown {
    return this.fs.comparable(query, answer);
  }
  initialContext(machine: string, input: Fields) {
    return this.fs.initialContext(machine, input);
  }
  guard(scope: Scope, records: RecordSource, transition: TransitionRef, extra: Fields, access: Access) {
    return this.fs.guard(scope, records, transition, extra, this.c.collecting(scope, access));
  }
  assign(
    scope: Scope,
    records: RecordSource,
    assignment: Assignment,
    extra: Fields,
    keys: readonly (readonly [string, number])[],
    access: Access,
  ) {
    return this.fs.assign(scope, records, assignment, extra, keys, this.c.collecting(scope, access));
  }
  input(
    scope: Scope,
    records: RecordSource,
    activity: { readonly keyword: string; readonly key: string },
    keys: readonly (readonly [string, number])[],
    access: Access,
  ) {
    return this.fs.input(scope, records, activity, keys, this.c.collecting(scope, access));
  }
  holds(scope: Scope, records: RecordSource, access: Access) {
    return this.fs.holds(scope, records, access);
  }
  deadlines(machine: string, state: string) {
    return this.fs.deadlines(machine, state);
  }
  deadlineAt(scope: Scope, records: RecordSource, name: string, access: Access) {
    return this.fs.deadlineAt(scope, records, name, this.c.collecting(scope, access));
  }
  offers(scope: Scope, records: RecordSource, control: string, access: Access) {
    return this.fs.offers(scope, records, control, this.c.collecting(scope, access));
  }
  showInput(
    scope: Scope,
    records: RecordSource,
    activity: { readonly keyword: string; readonly key: string },
    access: Access,
  ) {
    return this.fs.showInput(scope, records, activity, this.c.collecting(scope, access));
  }
  items(scope: Scope, records: RecordSource, access: Access) {
    return this.fs.items(scope, records, this.c.collecting(scope, access));
  }
  copyContext(machine: string, map: string): Fields {
    return this.fs.copyContext(machine, map);
  }
  singleRecord(entity: string) {
    return this.fs.singleRecord(entity);
  }
  copyKey(machine: string, map: string, payload: unknown) {
    return this.fs.copyKey(machine, map, payload);
  }
  close(scope: Scope, records: RecordSource, access: Access) {
    return this.fs.close(scope, records, this.c.collecting(scope, access));
  }
}
