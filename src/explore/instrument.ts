import { bagValues, enumerations } from "../data/bag.ts";
import type { BagOrderDependent } from "../data/bagOrderDependent.generated.ts";
import { emptyBinding, matchValue } from "../data/binding.ts";
import { Bag } from "../data/canonical.ts";
import type { StepName } from "../data/choiceDependent.generated.ts";
import type { DefinitionRef } from "../data/definitionRef.ts";
import type { Answer, TraceLine } from "../data/trace.generated.ts";
import type { TransitionRef } from "../data/transitionRef.ts";
import { byCodePoint, canonicalJson, type Fields, plain } from "../data/values.ts";
import { type Located, type ViolationError, withExtra } from "../data/violation.ts";
import { ref, refOf, type Schema, type Service } from "../service/basic.ts";
import {
  type Access,
  type Assignment,
  Failed,
  type Functions,
  givenKeys,
  type Holder,
  holderResource,
  type Keys,
  type Scope,
} from "../service/functions.ts";
import type { Emit } from "../service/message.ts";
import type { Note, RegionCheck, RegionPair } from "../service/note.ts";
import { normalizeOutput } from "../service/query.ts";
import type { RecordSource } from "../service/records.ts";
import type { State, StepInfo } from "../service/state.ts";
import { type Causes, channelOf, leadsTo, lineSteps } from "../sim/trace.ts";
import { contractsListing, named } from "../spec/structure.ts";

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

/** Lean's comparedEvent: whether the `out` line `l` is an event that a contract lists. */
function comparedEvent(st: Service, l: TraceLine): boolean {
  if (l.type !== "event") return false;
  const d = named(st.structure, st.service, l.name, ["event"]);
  return d !== undefined && contractsListing(st.structure, { service: d.service, name: d.name }).length > 0;
}

/** Lean's tiedDeadlines: whether steps `i` and `j` are deadlines of one tie. */
function tiedDeadlines(steps: readonly StepInfo[], i: number, j: number): boolean {
  const [a, b] = [steps[i]?.tie, steps[j]?.tie];
  return a !== undefined && b !== undefined && a.equals(b);
}

const reportedKey = (v: BagOrderDependent): string => JSON.stringify([v.kind, v.definition, v.data]);

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
      | "events"
      | "stepBegins"
      | "stepEnds"
      | "settlesAround"
      | "transitionPart"
      | "microstepEnds"
      | "afterMessageBegins"
      | "afterMessageEnds"
    >
{
  /** The definitions already reported by orderAudit, as JSON. */
  private readonly reportedOrder = new Set<string>();
  private transition: number | undefined;
  private readonly transitions = new Map<number, TransitionAccess>();
  /** For each step that began and has not ended, outermost first, the instance or copy that it starts. */
  private readonly openSteps: (string | undefined)[] = [];
  /** The access of each step that began while no step was open, by step number, in the order they began. */
  private readonly steps = new Map<number, StepAccess>();
  /** The access of the step open outermost, which began last of `steps`. */
  private outermost: StepAccess | undefined;
  /** The message whose afterMessage runs, while it runs. */
  private afterMessage: number | undefined;
  /** For each message, the values that its afterMessage read: subscription answers, holds, invariants, and rearm. */
  private readonly afters = new Map<number, Footprint>();
  readonly violations: (BagOrderDependent & Located)[] = [];
  /** The kind, definition and data of each of `violations`, which Lean's Violation compares. */
  private readonly reported = new Set<string>();
  readonly causes: Causes = { events: [] };

  /**
   * Returns a copy for the next input. Between inputs, no step and no microstep is open, and a closed step's access
   * does not change, so the copy shares them.
   */
  clone(): Collect {
    const copy = new Collect();
    for (const name of this.reportedOrder) copy.reportedOrder.add(name);
    for (const [step, access] of this.steps) copy.steps.set(step, access);
    for (const [message, access] of this.afters) copy.afters.set(message, access);
    copy.violations.push(...this.violations);
    for (const key of this.reported) copy.reported.add(key);
    copy.causes.events.push(...this.causes.events);
    return copy;
  }

  hasReportedOrder(definition: DefinitionRef): boolean {
    return this.reportedOrder.has(JSON.stringify(definition));
  }

  reportOrder(definition: DefinitionRef, v: BagOrderDependent & Located): void {
    this.reportedOrder.add(JSON.stringify(definition));
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

  private report(v: BagOrderDependent): void {
    const key = reportedKey(v);
    if (this.reported.has(key)) return;
    this.reported.add(key);
    this.violations.push(v);
  }

  events(step: number, start: number, groups: readonly number[]): void {
    let first = start;
    for (const count of groups) {
      this.causes.events.push([step, first, count]);
      first += count;
    }
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

  afterMessageBegins(message: number): void {
    this.afterMessage = message;
  }

  afterMessageEnds(): void {
    this.afterMessage = undefined;
  }

  /** Lean's stepAccess: the outermost open step, or, while no step is open, the afterMessage that runs. */
  private accessing(): Footprint | undefined {
    if (this.outermost !== undefined) return this.outermost;
    const message = this.afterMessage;
    if (message === undefined) return undefined;
    const after = this.afters.get(message) ?? { reads: new Set(), writes: new Set(), keyWrites: new Set() };
    this.afters.set(message, after);
    return after;
  }

  read(key: string): void {
    this.accessing()?.reads.add(key);
  }

  /**
   * Adds a write to the outermost open step, or to the afterMessage that runs. Writes to the instance or copy that an
   * open step starts, or to its copies, never overlap other steps.
   */
  write(key: string, keyWrite: boolean): void {
    const started = (resource: string | undefined) =>
      resource !== undefined &&
      (key.startsWith(`context:${resource}.`) ||
        key.startsWith(`context:${resource}@`) ||
        key.startsWith(`state:${resource}@`));
    if (this.openSteps.some(started)) return;
    const access = this.accessing();
    if (access !== undefined) (keyWrite ? access.keyWrites : access.writes).add(key);
  }

  /** Returns the name of each step from step `from` on that began while no step was open, in the order they began. */
  names(from: number): (readonly [number, StepName])[] {
    return [...this.steps].flatMap(([step, access]) => (step < from ? [] : [[step, access.name] as const]));
  }

  /** Lean's channelWrites: each channel that a compared event line writes, with the step of `steps` that wrote it. */
  private channelWrites(st: Service, s: State): (readonly [number, string])[] {
    const lines = lineSteps(s.lines.length, this.causes);
    const tops = [...this.steps.keys()];
    return s.lines.flatMap((l, i) => {
      const w = lines[i]?.[0];
      if (w === undefined || l.dir !== "out" || !comparedEvent(st, l)) return [];
      const t = tops.filter((k) => k <= w).at(-1);
      const channel = channelOf(l);
      return t === undefined || channel === undefined ? [] : [[t, channel] as const];
    });
  }

  /** Lean's involved: the footprint of what step `n` stands for when the search swaps its order. */
  private involved(s: State, channels: readonly (readonly [number, string])[], n: number, a: StepAccess): Footprint {
    const message = s.steps[n]?.message;
    const tied = s.steps[n]?.tie !== undefined;
    const steps: (readonly [number, StepAccess])[] = tied
      ? [...this.steps].filter(([k]) => s.steps[k]?.message === message)
      : [[n, a]];
    const numbers = new Set(steps.map(([k]) => k));
    const f: Footprint = {
      reads: new Set(),
      writes: new Set(channels.filter(([t]) => numbers.has(t)).map(([, c]) => c)),
      keyWrites: new Set(),
    };
    const after = tied && message !== undefined ? this.afters.get(message) : undefined;
    for (const x of [...(after === undefined ? [] : [after]), ...steps.map(([, x]) => x)]) {
      for (const v of x.reads) f.reads.add(v);
      for (const v of x.writes) f.writes.add(v);
      for (const v of x.keyWrites) f.keyWrites.add(v);
    }
    return f;
  }

  /** Returns Lean's candidates of a run that did not halt, of the steps from step `from` on. */
  candidates(st: Service, s: State, from: number): (readonly [number, number])[] {
    const channels = this.channelWrites(st, s);
    const footprints = new Map([...this.steps].map(([n, a]) => [n, this.involved(s, channels, n, a)] as const));
    const tagged = [...this.steps].filter(([step]) => step >= from);
    return tagged.flatMap(([i, a], n) =>
      tagged
        .slice(n + 1)
        .filter(
          ([j, b]) =>
            (tiedDeadlines(s.steps, i, j) || s.steps[i]?.message === s.steps[j]?.message) &&
            overlaps(footprints.get(i) as Footprint, footprints.get(j) as Footprint) &&
            !commutes(a, b) &&
            canonicalJson(a.name) !== canonicalJson(b.name) &&
            !leadsTo(s.steps, i, j),
        )
        .map(([j]) => [i, j] as const),
    );
  }
}

/**
 * Lean's InstrumentFunctions without lastReads and lastAccess, which the TS run tells as it reads, and lastEnumerated,
 * which `enumerations` tells. `reversed` returns what `call` answers with every Bag in reverse order, without telling
 * what it reads or reaching coverage.
 */
export interface InstrumentFunctions {
  reversed<T>(call: (fs: Functions) => T): T;
}

/** The Access of an answer asked again, which tells nothing. */
const silent: Access = { context: () => {}, active: () => {}, assigned: () => {}, shown: () => {}, now: () => {} };

/** Returns `value` with each Bag as the array of its values, as Lean's Value holds it. */
function unbagged(value: unknown): unknown {
  const values = bagValues(value);
  if (values !== undefined) return values.map(unbagged);
  if (Array.isArray(value)) return value.map(unbagged);
  if (value === null || typeof value !== "object" || Object.getPrototypeOf(value) !== Object.prototype) return value;
  return Object.fromEntries(Object.entries(value).map(([k, v]) => [k, unbagged(v)]));
}

/** Lean's canonical: the canonical JSON of a value whose Bags are arrays. */
const text = (value: unknown): string => canonicalJson(unbagged(value));

/** Lean's madeValue: a value with each array as a Bag. */
function madeValue(value: unknown): unknown {
  if (Array.isArray(value)) return new Bag(value.map(madeValue));
  if (value === null || typeof value !== "object") return value;
  return Object.fromEntries(Object.entries(value).map(([k, v]) => [k, madeValue(v)]));
}

/** What an audit compares of two answers: the texts that a function gives them, or a relation (Lean's `same`). */
type Same<T> = ((answer: T) => string) | { readonly same: (a: T, b: T) => boolean };

/** Lean's sameMade: whether two values that calls made are equal up to a renaming of the keys that they created. */
function sameMade(keys: Keys, a: readonly [unknown, readonly string[]], b: readonly [unknown, readonly string[]]) {
  const entities = (created: readonly string[]) => canonicalJson(created.toSorted(byCodePoint));
  if (entities(a[1]) !== entities(b[1])) return false;
  if (a[1].length === 0) return text(a[0]) === text(b[0]);
  const domains = new Map(givenKeys(keys, a[1]).map(([entity, key]) => [key, entity]));
  const others = new Map(givenKeys(keys, b[1]).map(([entity, key]) => [key, entity]));
  const values = {
    domain: (s: string) => domains.get(s) ?? "",
    fresh: new Set(domains.keys()),
    image: (s: string, t: string) => others.get(t) === domains.get(s),
  };
  const found = matchValue(values, emptyBinding, madeValue(plain(unbagged(a[0]))), madeValue(plain(unbagged(b[0]))));
  return found !== undefined && found.length > 0;
}

/** Lean's textSet: the texts without order or repetition. */
const textSet = (texts: readonly string[]): string => canonicalJson([...new Set(texts)].toSorted(byCodePoint));

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
   * Lean's `audit` in `instrument`: returns what `answer` answers and, when that call ran a Bag callback, audits the
   * answer as orderAudit does, asking `again` of the functions with Bags in reverse order and telling the two answers
   * apart by `compared`.
   */
  private audited<T>(
    definition: DefinitionRef,
    question: string,
    answer: () => T | Failed,
    again: (fs: Functions) => T | Failed,
    compared: Same<T>,
  ): T | Failed {
    const before = enumerations();
    const answered = answer();
    if (answered instanceof Failed || enumerations() === before || this.c.hasReportedOrder(definition)) return answered;
    const reversed = this.ifs.reversed(again);
    const data = { function: question };
    if (reversed instanceof Failed)
      this.c.reportOrder(
        definition,
        withExtra({ kind: "BagOrderDependent.reversedException", definition, data }, { error: reversed.error }),
      );
    else if (
      !(typeof compared === "function" ? compared(answered) === compared(reversed) : compared.same(answered, reversed))
    )
      this.c.reportOrder(definition, { kind: "BagOrderDependent.reversedResult", definition, data });
    return answered;
  }

  /** Lean's audited for a question about a chart, whose access goes to the open transition part. */
  private chartAudited<T>(
    scope: Scope,
    access: Access,
    question: string,
    call: (fs: Functions, access: Access) => T | Failed,
    compared: Same<T>,
  ): T | Failed {
    return this.audited(
      ref(this.st, scope.machine),
      question,
      () => call(this.fs, this.c.collecting(scope, access)),
      (fs) => call(fs, silent),
      compared,
    );
  }

  /** Lean's resolveCollect. */
  private resolveAudit(name: string, input: Fields, records: RecordSource, now: Temporal.Instant, resolved: unknown) {
    const definition = ref(this.st, name);
    if (this.c.hasReportedOrder(definition)) return;
    const checked = normalizeOutput(this.st, this.fs, name, resolved);
    if (checked instanceof Failed || "error" in checked) return;
    const original = this.fs.comparable(name, { result: "fulfilled", output: checked.encoded });
    if (original instanceof Failed) return;
    const data = { function: "resolve" };
    const exception = (error: ViolationError | undefined) =>
      this.c.reportOrder(
        definition,
        withExtra({ kind: "BagOrderDependent.reversedException", definition, data }, { error }),
      );
    const reversed = this.ifs.reversed((fs) => fs.resolve(name, input, records, now));
    if (reversed instanceof Failed) return exception(reversed.error);
    const normalized = normalizeOutput(this.st, this.fs, name, reversed);
    if (normalized instanceof Failed || "error" in normalized) return exception(normalized.error);
    const reordered = this.fs.comparable(name, { result: "fulfilled", output: normalized.encoded });
    if (reordered instanceof Failed) return exception(reordered.error);
    if (canonicalJson(original) !== canonicalJson(reordered))
      this.c.reportOrder(definition, { kind: "BagOrderDependent.reversedResult", definition, data });
  }

  parse(schema: Schema, value: unknown) {
    return this.fs.parse(schema, value);
  }
  canonical(schema: Schema, value: unknown): unknown {
    return this.fs.canonical(schema, value);
  }
  unordered(schema: Schema, value: unknown): unknown {
    return this.fs.unordered(schema, value);
  }
  normalize(schema: Schema, value: unknown) {
    return this.fs.normalize(schema, value);
  }
  binding(command: string, binding: string, input: Fields, records: RecordSource, now: Temporal.Instant) {
    const call = (fs: Functions) => fs.binding(command, binding, input, records, now);
    return this.audited(ref(this.st, command), "binding", () => call(this.fs), call, String);
  }
  requirement(command: string, condition: string, input: Fields, records: RecordSource, now: Temporal.Instant) {
    const call = (fs: Functions) => fs.requirement(command, condition, input, records, now);
    return this.audited(ref(this.st, command), "requirement", () => call(this.fs), call, String);
  }
  inputRequirement(target: string, condition: string, input: Fields) {
    const call = (fs: Functions) => fs.inputRequirement(target, condition, input);
    return this.audited(refOf(this.st, target), "inputRequirement", () => call(this.fs), call, String);
  }
  decide(command: string, input: Fields, records: RecordSource, now: Temporal.Instant) {
    const call = (fs: Functions) => fs.decide(command, input, records, now);
    const groupTexts = (groups: readonly (readonly Emit[])[]) =>
      canonicalJson(
        groups.map((g) => g.map((e) => text({ event: e.event, payload: e.payload })).toSorted(byCodePoint)),
      );
    return this.audited(ref(this.st, command), "decide", () => call(this.fs), call, groupTexts);
  }
  ensures(command: string, input: Fields, before: RecordSource, after: RecordSource, now: Temporal.Instant) {
    const call = (fs: Functions) => fs.ensures(command, input, before, after, now);
    return this.audited(ref(this.st, command), "ensures", () => call(this.fs), call, String);
  }
  queryEnsures(query: string, input: Fields, output: Fields, records: RecordSource) {
    const call = (fs: Functions) => fs.queryEnsures(query, input, output, records);
    return this.audited(ref(this.st, query), "queryEnsures", () => call(this.fs), call, String);
  }
  resultEnsures(target: string, input: Fields, output: unknown, events: readonly Emit[]) {
    const call = (fs: Functions) => fs.resultEnsures(target, input, output, events);
    return this.audited(refOf(this.st, target), "resultEnsures", () => call(this.fs), call, String);
  }
  invariant(entity: string, record: Fields) {
    const call = (fs: Functions) => fs.invariant(entity, record);
    return this.audited(ref(this.st, entity), "invariant", () => call(this.fs), call, String);
  }
  serviceInvariant(records: RecordSource) {
    return this.fs.serviceInvariant(records);
  }
  chartInvariant(scope: Scope, records: RecordSource, access: Access) {
    return this.audited(
      ref(this.st, scope.machine),
      "chartInvariant",
      () => this.fs.chartInvariant(scope, records, access),
      (fs) => fs.chartInvariant(scope, records, silent),
      String,
    );
  }
  resolve(query: string, input: Fields, records: RecordSource, now: Temporal.Instant): unknown {
    const before = enumerations();
    const resolved = this.fs.resolve(query, input, records, now);
    if (!(resolved instanceof Failed) && enumerations() !== before)
      this.resolveAudit(query, input, records, now, resolved);
    return resolved;
  }
  react(automation: string, payload: Fields, records: RecordSource, now: Temporal.Instant, keys: Keys) {
    const call = (fs: Functions) => fs.react(automation, payload, records, now, keys);
    return this.audited(ref(this.st, automation), "react", () => call(this.fs), call, {
      same: (x, y) => sameMade(keys, [x.input ?? null, x.created], [y.input ?? null, y.created]),
    });
  }
  comparable(query: string, answer: Answer): unknown {
    return this.fs.comparable(query, answer);
  }
  initialContext(machine: string, input: Fields) {
    const call = (fs: Functions) => fs.initialContext(machine, input);
    return this.audited(ref(this.st, machine), "initialContext", () => call(this.fs), call, text);
  }
  guard(scope: Scope, records: RecordSource, transition: TransitionRef, extra: Fields, access: Access) {
    return this.chartAudited(scope, access, "guard", (fs, a) => fs.guard(scope, records, transition, extra, a), String);
  }
  assign(scope: Scope, records: RecordSource, assignment: Assignment, extra: Fields, keys: Keys, access: Access) {
    return this.chartAudited(
      scope,
      access,
      "assign",
      (fs, a) => fs.assign(scope, records, assignment, extra, keys, a),
      {
        same: (x, y) =>
          sameMade(
            keys,
            [[x.context, x.copyContext ?? null], x.created],
            [[y.context, y.copyContext ?? null], y.created],
          ),
      },
    );
  }
  input(
    scope: Scope,
    records: RecordSource,
    activity: { readonly keyword: string; readonly key: string },
    keys: Keys,
    access: Access,
  ) {
    return this.chartAudited(scope, access, "input", (fs, a) => fs.input(scope, records, activity, keys, a), {
      same: (x, y) => sameMade(keys, [x.encoded, x.created], [y.encoded, y.created]),
    });
  }
  holds(scope: Scope, records: RecordSource, access: Access) {
    return this.audited(
      ref(this.st, scope.machine),
      "holds",
      () => this.fs.holds(scope, records, access),
      (fs) => fs.holds(scope, records, silent),
      () => "",
    );
  }
  deadlines(machine: string, state: string) {
    return this.fs.deadlines(machine, state);
  }
  deadlineAt(scope: Scope, records: RecordSource, name: string, access: Access) {
    return this.chartAudited(scope, access, "deadlineAt", (fs, a) => fs.deadlineAt(scope, records, name, a), String);
  }
  offers(scope: Scope, records: RecordSource, control: string, access: Access) {
    return this.chartAudited(
      scope,
      access,
      "offers",
      (fs, a) => fs.offers(scope, records, control, a),
      (payloads) => textSet(payloads.map((p) => canonicalJson(p.encoded))),
    );
  }
  showInput(
    scope: Scope,
    records: RecordSource,
    activity: { readonly keyword: string; readonly key: string },
    access: Access,
  ) {
    return this.chartAudited(
      scope,
      access,
      "showInput",
      (fs, a) => fs.showInput(scope, records, activity, a),
      ({ encoded }) => canonicalJson(encoded),
    );
  }
  items(scope: Scope, records: RecordSource, access: Access) {
    return this.chartAudited(
      scope,
      access,
      "items",
      (fs, a) => fs.items(scope, records, a),
      (keys) => textSet(keys.map((k) => k.encodedKey)),
    );
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
    return this.chartAudited(
      scope,
      access,
      "close",
      (fs, a) => fs.close(scope, records, a),
      ({ output, failed }) => text([output, failed ?? null]),
    );
  }
}
