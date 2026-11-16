import { reversedBags } from "../../data/bag.ts";
import { alike } from "../../data/canonical.ts";
import type { StepName } from "../../data/choiceDependent.generated.ts";
import type { DefinitionRef } from "../../data/definitionRef.ts";
import type { Step } from "../../data/step.generated.ts";
import type { DeadlineId, TraceLine } from "../../data/trace.generated.ts";
import type { Obligation } from "../../data/uncovered.ts";
import type { Violation } from "../../data/violation.ts";
import type { AnyCommand, AnyQuery, Place } from "../../dsl/definition.ts";
import type { Input } from "../../dsl/scenario.ts";
import { placeOf } from "../../load/found.ts";
import type { Spec } from "../../load/load.ts";
import { definitionOfTraceName, traceName } from "../../load/traceName.ts";
import { type Enabled, enabled } from "../../observe/enabled.ts";
import {
  Collect,
  contextKey,
  InstrumentedFunctions,
  type InstrumentFunctions,
  shownKey,
} from "../../observe/instrument.ts";
import { snapshotLines } from "../../observe/trace.ts";
import type { Activity } from "../../service/chart/basic.ts";
import type { Processing } from "../../service/chart/queue.ts";
import { type Note, type RecordPart, type RegionCheck, recordPartName, stateValueName } from "../../service/note.ts";
import type { Records } from "../../service/records.ts";
import { given, step } from "../../service/run.ts";
import {
  type Evaluations,
  Halt,
  machine,
  type Pending,
  type State,
  type StepInfo,
  senderOf,
} from "../../service/state.ts";
import { Cache } from "./cache.ts";
import { clone } from "./copy.ts";
import { Coverage } from "./coverage.ts";
import { fingerprint } from "./fingerprint.ts";
import { SpecFunctions } from "./functions.ts";
import { newProcessing } from "./processing.ts";

export interface Outcome {
  readonly lines: readonly TraceLine[];
  readonly violations: readonly Violation[];
}

export class Run {
  readonly outcome: Outcome;
  /** The state after the last input, which extend continues. */
  readonly execution: Execution;
  readonly halted: Violation | undefined;
  /** What can happen next in the state after the last input; undefined when the run halted or took no input. */
  readonly enabled: Enabled | undefined;

  constructor(execution: Execution, fed: Fed) {
    const { processing: r } = execution;
    const { collected } = execution.listener;
    const s = r.state;
    this.execution = execution;
    this.outcome = {
      lines: snapshotLines(
        s.lines,
        s.steps,
        s.messageCount,
        collected.causes,
        s.created.map(([, key]) => key),
      ),
      violations: [...s.violations, ...collected.violations, ...("halted" in fed ? [fed.halted] : [])],
    };
    this.halted = "halted" in fed ? fed.halted : undefined;
    this.enabled = "enabled" in fed ? fed.enabled : undefined;
  }

  /**
   * The request that each input answered, or undefined for an input that is not an answer or an answer that answered no
   * request.
   */
  get answered(): readonly (Pending | undefined)[] {
    return this.execution.answered;
  }
  /** The trace line count when each input arrives, after the deadlines due by its time. */
  get inputLines(): readonly number[] {
    return this.execution.inputLines;
  }
  /**
   * Returns the index of the input during which the run reported `violation`, one of the state's violations or the one
   * that halted the run, or undefined for another violation.
   */
  inputOf(violation: Violation): number | undefined {
    const last = this.execution.inputs.length - 1;
    if (violation === this.halted) return last;
    const j = this.execution.processing.state.violations.indexOf(violation);
    if (j < 0) return undefined;
    const k = this.execution.violationCounts.findIndex((count) => count > j);
    return k < 0 ? last : k;
  }
  /**
   * Returns the violations of outcome.violations that `parent`, which this run extends, did not report. The run's
   * violations and the OrderDependent violations each keep the parent's as their start.
   */
  violationsSince(parent: Run): Violation[] {
    const [s, p] = [this.execution.processing.state, parent.execution.processing.state];
    const [collected, parentCollected] = [this.execution.listener.collected, parent.execution.listener.collected];
    const reported = s.violations.length + collected.violations.length;
    return [
      ...s.violations.slice(p.violations.length),
      ...collected.violations.slice(parentCollected.violations.length),
      ...this.outcome.violations.slice(reported),
    ];
  }
  get now(): Temporal.Instant {
    return this.execution.processing.state.now;
  }
  get coverage(): Coverage {
    return this.execution.listener.coverage;
  }
  get requestPairs(): readonly RequestPair[] {
    return this.execution.listener.pairs;
  }
  get records(): Records {
    return this.execution.processing.state.records;
  }
  /** The steps of the run, as its causes and messages order them. */
  get steps(): readonly StepInfo[] {
    return this.execution.processing.state.steps;
  }
  /**
   * Returns the steps from step `from` on that began while no step was open, with their names, in the order they began;
   * and the pairs among them whose other order explore runs (Lean's candidates), none when the run halted.
   */
  stepsFrom(from: number): {
    readonly names: readonly (readonly [number, StepName])[];
    readonly candidates: readonly (readonly [number, number])[];
  } {
    const { collected } = this.execution.listener;
    return {
      names: collected.names(from),
      candidates: this.halted === undefined ? collected.candidates(this.steps, from) : [],
    };
  }
  /** The ids of the subscriptions that other services hold on this service's queries. */
  get openSubscriptions(): readonly string[] {
    return this.execution.processing.state.subscriptions.entries().map(([id]) => id);
  }
  /**
   * The deadlines of the first tie, since the run that this run extends, in which `deadlineOrder` had no entry left, so
   * the first of them fired.
   */
  get unchosenDeadlines(): readonly DeadlineId[] | undefined {
    return this.execution.listener.unchosen;
  }
  fingerprint(): string {
    return fingerprint(this.execution.processing);
  }
  waits(id: string): boolean {
    return this.execution.processing.state.pending.some((p) => p.id === id);
  }
  /** Returns the other waiting requests that the trace cannot tell from request `id`, with their senders. */
  alikeRequests(id: string): { readonly id: string; readonly sender: unknown }[] {
    const { processing: r, listener } = this.execution;
    const s = r.state;
    const request = s.pending.find((p) => p.id === id);
    if (request === undefined) return [];
    const senderAt = (p: Pending) =>
      definitionOfTraceName(listener.spec, r.st.service, senderOf(s, p.requester), "machine", "screen", "automation");
    return alikeTo(s, request)
      .slice(1)
      .map((p) => ({ id: p.id, sender: senderAt(p) }));
  }
  /** Returns the chart of the instance or copy whose resource is `resource`, or null when the run has none. */
  chartOf(resource: string): DefinitionRef | null {
    const r = this.execution.processing;
    const instance = machine(r.state, resource);
    return instance === undefined ? null : { service: r.st.service, name: instance.chart.name };
  }
}

/**
 * Returns the request, then, in sending order, the others that the trace cannot tell from it, so that an implementation
 * may give an answer to any of them: other requests with equal type, name and input, written at the same time with no
 * input line between, that no line names yet. A request without a request line has no such others.
 */
function alikeTo(s: State, request: Pending): Pending[] {
  const { lines } = s;
  const line = (p: Pending) => lines.findIndex((l) => l.dir === "out" && l.id === p.id);
  const lineNames = (p: Pending) => lines.some((l) => "to" in l && l.to === p.id);
  const at = line(request);
  if (at < 0 || lineNames(request)) return [request];
  const together = (other: number) =>
    lines[other]?.time === lines[at]?.time &&
    !lines.slice(Math.min(at, other), Math.max(at, other)).some((l) => l.dir === "in");
  return [
    request,
    ...s.pending.filter((p) => {
      const other = line(p);
      return (
        p !== request &&
        p.stale === request.stale &&
        other >= 0 &&
        alike(lines[other] as TraceLine, lines[at] as TraceLine) &&
        !lineNames(p) &&
        together(other)
      );
    }),
  ];
}

const copiedKeys = (keys: Readonly<Record<string, readonly string[]>>) =>
  Object.fromEntries(Object.entries(keys).map(([e, names]) => [e, [...names]]));

/** Returns the handle of a named input, which check makes sure that the run places (Illegal.namedInputUnplaced). */
function handleOf(named: { readonly handle?: string }): string {
  if (named.handle === undefined) throw new Error("a line names an input that its run does not place");
  return named.handle;
}

function stepOf(spec: Spec, service: string, input: Input): Step {
  const name = (d: unknown) => traceName(spec, d, service);
  function body(): Step {
    const { time } = input;
    switch (input.type) {
      case "time":
      case "restart":
        return { time, type: input.type };
      case "command":
        return { time, type: "command", ...given(input), name: name(input.command), input: input.input };
      case "query":
        return { time, type: input.type, ...given(input), name: name(input.query), input: input.input };
      case "subscribe":
        return {
          time,
          type: input.type,
          ...given(input),
          name: name(input.query),
          input: input.input,
          ...(input.handle === undefined ? {} : { handle: input.handle }),
        };
      case "event":
        return {
          time,
          type: "event",
          ...given(input),
          name: name(input.event),
          payload: input.payload,
          ...(input.resultOf === undefined ? {} : { resultOf: handleOf(input.resultOf) }),
        };
      case "operation":
      case "unacceptedOperation":
        return { time, type: input.type, screen: name(input.screen), control: input.control, payload: input.payload };
      case "unsubscribe":
        return {
          time,
          type: "unsubscribe",
          subscription: "to" in input ? { to: input.to } : { handle: handleOf(input.subscription) },
        };
      case "answerById":
        return { time, type: "answerById", to: input.to, target: name(input.target), answer: input.answer };
      case "answer":
        return {
          time,
          type: "answer",
          sender: name(input.sender),
          target: name(input.target),
          answer: input.answer,
          ...(input.choice === undefined ? {} : { choice: input.choice }),
          ...(input.handle === undefined ? {} : { handle: input.handle }),
        };
    }
  }
  return {
    ...body(),
    ...(input.deadlineOrder === undefined ? {} : { deadlineOrder: [...input.deadlineOrder] }),
    ...(input.stepOrder === undefined ? {} : { stepOrder: [...input.stepOrder] }),
    ...("keys" in input && input.keys !== undefined ? { keys: copiedKeys(input.keys) } : {}),
    ...(input.advanceKeys === undefined ? {} : { advanceKeys: copiedKeys(input.advanceKeys) }),
  };
}

/** Returns the inputs of `steps`, as stepsOf would give them back; each resultOf names the latest answer with its handle. */
export function inputsOf(spec: Spec, service: string, steps: readonly Step[]): Input[] {
  const inputs: Input[] = [];
  const handled = new Map<string, Input>();
  const named = <K extends Parameters<typeof definitionOfTraceName>[3]>(name: string, ...kinds: K[]) => {
    const found = definitionOfTraceName(spec, service, name, ...kinds);
    if (found === undefined) throw new Error(`no ${kinds.join(" or ")} ${name} from ${service}`);
    return found;
  };
  for (const s of steps) {
    const scheduled = {
      ...(s.deadlineOrder === undefined ? {} : { deadlineOrder: s.deadlineOrder }),
      ...(s.stepOrder === undefined ? {} : { stepOrder: s.stepOrder }),
      ...(s.keys === undefined ? {} : { keys: s.keys }),
      ...(s.advanceKeys === undefined ? {} : { advanceKeys: s.advanceKeys }),
    };
    const { time } = s;
    const body = (): Input => {
      switch (s.type) {
        case "time":
        case "restart":
          return { time, type: s.type };
        case "command":
          return { time, type: "command", ...given(s), command: named(s.name, "command"), input: s.input };
        case "query":
          return { time, type: s.type, ...given(s), query: named(s.name, "query"), input: s.input };
        case "subscribe":
          return {
            time,
            type: s.type,
            ...given(s),
            query: named(s.name, "query"),
            input: s.input,
            ...(s.handle === undefined ? {} : { handle: s.handle }),
          };
        case "unsubscribe": {
          if ("to" in s.subscription) return { time, type: "unsubscribe", to: s.subscription.to };
          const subscription = handled.get(s.subscription.handle);
          if (subscription?.type !== "subscribe") throw new Error("unsubscribe names no subscribe handle");
          return { time, type: "unsubscribe", subscription };
        }
        case "event": {
          const resultOf = s.resultOf === undefined ? undefined : handled.get(s.resultOf);
          if (s.resultOf !== undefined && resultOf === undefined) throw new Error("resultOf names no answer handle");
          return {
            time,
            type: "event",
            ...given(s),
            event: named(s.name, "event"),
            payload: s.payload,
            ...(resultOf === undefined ? {} : { resultOf }),
          } as Input;
        }
        case "operation":
        case "unacceptedOperation":
          return { time, type: s.type, screen: named(s.screen, "screen"), control: s.control, payload: s.payload };
        case "answerById":
          return { time, type: "answerById", to: s.to, target: named(s.target, "command", "query"), answer: s.answer };
        case "answer":
          return {
            time,
            type: "answer",
            sender: named(s.sender, "machine", "screen", "automation"),
            target: named(s.target, "command", "query"),
            answer: s.answer,
            ...(s.choice === undefined ? {} : { choice: s.choice }),
            ...(s.handle === undefined ? {} : { handle: s.handle }),
          } as Input;
      }
    };
    const input = { ...body(), ...scheduled } as Input;
    if ((s.type === "answer" || s.type === "subscribe") && s.handle !== undefined) handled.set(s.handle, input);
    inputs.push(input);
  }
  return inputs;
}

export function stepsOf(spec: Spec, service: string, inputs: readonly Input[]): Step[] {
  return inputs.map((input) => stepOf(spec, service, input));
}

/** Two requests to a spec service: `second` was sent while `first` awaited its answer. */
export interface RequestPair {
  readonly first: AnyCommand | AnyQuery;
  readonly second: AnyCommand | AnyQuery;
  readonly place: Place;
}

/** The evaluation cache's name for the time, which no value's key can be. */
const now = "@now";

/**
 * The note that a TS run listens with: Lean's Collect, the evaluation cache (which the reads and writes keep current),
 * and the coverage hits, request pairs and unchosen tie that explore reads. It turns each note into the values that
 * both Collect and the evaluation cache hear.
 */
export class Listener implements Note, Evaluations {
  readonly spec: Spec;
  private readonly service: string;
  readonly collected: Collect;
  private readonly cache: Cache;
  readonly coverage: Coverage;
  readonly pairs: RequestPair[];
  /** The deadlines of the first unchosen tie since the clone; a clone starts without one. */
  unchosen: readonly DeadlineId[] | undefined;

  constructor(
    spec: Spec,
    service: string,
    collected: Collect,
    cache = new Cache(),
    coverage = new Coverage(),
    pairs: RequestPair[] = [],
  ) {
    this.spec = spec;
    this.service = service;
    this.collected = collected;
    this.cache = cache;
    this.coverage = coverage;
    this.pairs = pairs;
  }

  /** Returns a copy to continue between inputs, as Collect.clone does. */
  clone(): Listener {
    return new Listener(this.spec, this.service, this.collected.clone(), this.cache.clone(), this.coverage.clone(), [
      ...this.pairs,
    ]);
  }

  /** Records a read of `key`. Inside `quietly` no read counts, so the callers skip building the key. */
  private read(key: string): void {
    this.cache.read(key);
    this.collected.read(key);
  }

  private write(key: string, keyWrite: boolean): void {
    this.cache.wrote(key);
    this.collected.write(key, keyWrite);
  }

  events(step: number, start: number, groups: readonly number[]): void {
    this.collected.events(step, start, groups);
  }
  deadline(message: number, time: Temporal.Instant): void {
    this.collected.deadline(message, time);
  }
  stepBegins(step: number, name: StepName, startedResource: string | undefined): void {
    this.collected.stepBegins(step, name, startedResource);
  }
  stepEnds(): void {
    this.collected.stepEnds();
  }
  settlesAround(owner: string): void {
    this.collected.settlesAround(owner);
  }
  readStates(states: readonly (readonly [string, string])[]): void {
    if (!this.cache.quiet) for (const [resource, state] of states) this.read(stateValueName(resource, state));
  }
  wroteState(resource: string, state: string): void {
    this.write(stateValueName(resource, state), false);
  }
  wroteCopies(resource: string, map: string): void {
    this.write(stateValueName(resource, map), false);
  }
  wroteShown(resource: string, slot: string): void {
    this.write(shownKey(resource, slot), false);
  }
  transitionPart(part: number): void {
    this.collected.transitionPart(part);
  }
  microstepEnds(check: RegionCheck): void {
    this.collected.microstepEnds(check);
  }
  readRecord(part: RecordPart): void {
    if (!this.cache.quiet) this.read(recordPartName(part));
  }
  wroteRecord(part: RecordPart, keyWrite: boolean): void {
    this.write(recordPartName(part), keyWrite);
  }
  readContext(resource: string, field: string): void {
    if (!this.cache.quiet) this.read(contextKey(resource, field));
  }
  wroteContext(resource: string, field: string): void {
    this.write(contextKey(resource, field), false);
  }
  readShown(resource: string, slot: string): void {
    if (!this.cache.quiet) this.read(shownKey(resource, slot));
  }
  readNow(): void {
    if (!this.cache.quiet) this.cache.read(now);
  }
  wroteNow(): void {
    this.cache.wrote(now);
  }

  reached(obligation: Obligation): void {
    this.coverage.reach(obligation);
  }

  /**
   * Records the pairs of each waiting request and `activity`. A spec service may receive a waiting request and one sent
   * meanwhile in either order, which requestOrder compares.
   */
  requested(activity: Activity, sender: string, waiting: readonly Activity[]): void {
    const target = (a: Activity) =>
      definitionOfTraceName(this.spec, this.service, a.target, "command", "query") as AnyCommand | AnyQuery;
    const second = target(activity);
    if (second.service.external) return;
    for (const w of waiting)
      if (w.service === activity.service)
        this.pairs.push({
          first: target(w),
          second,
          place: placeOf(this.spec, { service: this.service, name: sender }),
        });
  }

  unchosenTie(deadlines: readonly DeadlineId[]): void {
    this.unchosen ??= deadlines;
  }

  replayIfFresh(resource: string, part: string): boolean {
    const reads = this.cache.freshReads(resource, part);
    if (reads === undefined) return false;
    if (!this.cache.quiet)
      for (const key of reads) {
        if (key === now) this.readNow();
        else this.read(key);
      }
    return true;
  }
  track(f: () => void): string[] {
    return this.cache.track(f);
  }
  remember(resource: string, part: string, reads: readonly string[], watched: readonly string[]): void {
    this.cache.remember(resource, part, reads, watched);
  }
  quietly<T>(f: () => T): T {
    return this.cache.quietly(f);
  }
}

/**
 * Returns Lean's `instrument st fs ifs` over the spec's functions. A question asked again with Bags in reverse order
 * reads quietly, so neither the open step nor the evaluation cache hears its reads, and it asks functions without the
 * listener, so that it reaches no coverage.
 */
export function instrumented(spec: Spec, service: string, listener: Listener): InstrumentedFunctions {
  const functions = new SpecFunctions(spec, service, listener);
  const unheard = new SpecFunctions(spec, service);
  const reversed: InstrumentFunctions["reversed"] = (call) => listener.quietly(() => reversedBags(() => call(unheard)));
  return new InstrumentedFunctions(functions.st, functions, { reversed }, listener.collected);
}

/**
 * The state of a run between inputs: the processing, the listener that listens to it, and what the run recorded so
 * far. A Run never changes its Execution; extend continues a clone.
 */
class Execution {
  readonly processing: Processing;
  readonly listener: Listener;
  /** The inputs fed so far, in order: a later input's resultOf names one of them. */
  readonly inputs: Input[];
  readonly answered: (Pending | undefined)[];
  readonly inputLines: number[];
  /** The number of the state's violations after each input that completed. */
  readonly violationCounts: number[];

  private constructor(
    processing: Processing,
    listener: Listener,
    inputs: Input[],
    answered: (Pending | undefined)[],
    inputLines: number[],
    violationCounts: number[],
  ) {
    this.processing = processing;
    this.listener = listener;
    this.inputs = inputs;
    this.answered = answered;
    this.inputLines = inputLines;
    this.violationCounts = violationCounts;
  }

  static create(spec: Spec, service: string): Execution {
    const listener = new Listener(spec, service, new Collect());
    const functions = instrumented(spec, service, listener);
    const place = spec.services.get(service)?.place;
    return new Execution(newProcessing(functions.st, functions, listener, place), listener, [], [], [], []);
  }

  /** Returns a copy; call it only after an input that completed without halting. */
  clone(): Execution {
    const listener = this.listener.clone();
    const functions = instrumented(listener.spec, this.processing.st.service, listener);
    return new Execution(
      clone(this.processing, functions, listener),
      listener,
      [...this.inputs],
      [...this.answered],
      [...this.inputLines],
      [...this.violationCounts],
    );
  }
}

/** The violation that halted the run, or what is enabled after the inputs, if any. */
type Fed = { readonly halted: Violation } | { readonly enabled: Enabled | undefined };

/**
 * Feeds the inputs in order. Enabled is computed after the last input, if any, since evaluating it can halt the run.
 */
function feed(execution: Execution, inputs: readonly Input[]): Fed {
  const { processing: r, listener } = execution;
  try {
    for (const input of inputs) {
      const next = stepOf(listener.spec, r.st.service, input);
      execution.inputs.push(input);
      execution.answered.push(step(r, next, (line) => execution.inputLines.push(line)));
      execution.violationCounts.push(r.state.violations.length);
    }
    return { enabled: inputs.length === 0 ? undefined : enabled(r) };
  } catch (error) {
    if (error instanceof Halt) return { halted: error.violation };
    throw error;
  }
}

export function execute(spec: Spec, service: string, inputs: readonly Input[]): Run {
  const execution = Execution.create(spec, service);
  return new Run(execution, feed(execution, inputs));
}

/**
 * Returns the outcome that execute gives for the run's inputs followed by `input`, continued from a copy of the run's
 * state instead of run again from the start. A halted run takes no more inputs, as in execute, so it is returned
 * unchanged.
 */
export function extend(run: Run, input: Input): Run {
  if (run.halted !== undefined) return run;
  const execution = run.execution.clone();
  return new Run(execution, feed(execution, [input]));
}
