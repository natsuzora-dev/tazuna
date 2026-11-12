import type { StepName } from "../data/choiceDependent.generated.ts";
import type { DefinitionRef } from "../data/definitionRef.ts";
import type { DeadlineId } from "../data/trace.generated.ts";
import type { TransitionRef } from "../data/transitionRef.ts";
import type { Obligation } from "../data/uncovered.ts";
import type { Activity } from "./chart/basic.ts";

/**
 * A part of the records: the entity's key set when there is no key and no field, the record's existence when there is
 * a key only, and the field's value when there is a field.
 */
export interface RecordPart {
  readonly entity: string;
  readonly key?: string;
  readonly field?: string;
}

/** Returns the key of the record part. Keys of different kinds of value differ in their first word. */
export function recordPartName({ entity, key, field }: RecordPart): string {
  if (field !== undefined) return `field:${entity}${key === undefined ? "" : `#${key}`}.${field}`;
  return key === undefined ? `keys:${entity}` : `record:${entity}#${key}`;
}

/** Returns the key of being in state `state` of the instance or copy whose resource is `holder`. */
export function stateValueName(holder: string, state: string): string {
  return `state:${holder}@${state}`;
}

export function stepNameDefinition(name: StepName): DefinitionRef {
  switch (name.kind) {
    case "reaction":
      return name.automation;
    case "command":
    case "answer":
      return name.sender.chart;
    default:
      return name.who.chart;
  }
}

/** The transitions `first` and `second` of one microstep, in different regions or copies of state `state`. */
export interface RegionPair {
  readonly first: number;
  readonly second: number;
  readonly firstRef: TransitionRef;
  readonly secondRef: TransitionRef;
  readonly state: string;
}

/** Lean's RegionCheck without `halted`: a microstep that halts throws before it ends. */
export interface RegionCheck {
  readonly chart: DefinitionRef;
  readonly pairs: readonly RegionPair[];
}

/**
 * What the run tells the instrumentation. The members return nothing: the run depends on who listens only through
 * Run's `evaluations`, which hears writes here.
 *
 * Differences from Note.lean:
 * - readRecord, wroteRecord, readContext, wroteContext, and readShown are TS only. Lean collects the values that spec
 *   functions read and write by wrapping Functions; the TS run calls the spec's functions itself and reports each value
 *   as it reads or writes it.
 * - Lean's `read` (record parts read without asking Functions) has no member: readRecord reports those reads too.
 * - readNow and wroteNow are TS only: reading and advancing the time, which only the evaluation cache hears, since
 *   the time advances only between steps.
 * - reached, requested and unchosenTie are TS only: the coverage hits that explore reads, the requests sent while
 *   others await an answer, whose orders explore compares (requestOrder), and the ties whose other orders explore runs
 *   (deadlineOrder).
 */
export interface Note {
  /** Reports that step `step` wrote `count` event lines from line `start`. */
  events(step: number, start: number, count: number): void;
  /** Reports that message `message` is the deadline message for time `time`. */
  deadline(message: number, time: Temporal.Instant): void;
  stepBegins(step: number, name: StepName, startedResource: string | undefined): void;
  stepEnds(): void;
  /**
   * Reports that the open step evaluates the always transitions of `owner` and its copies before and after its work.
   */
  settlesAround(owner: string): void;
  /** Reports that the open step read whether instances or copies, given by resource, are in states. */
  readStates(states: readonly (readonly [string, string])[]): void;
  wroteState(resource: string, state: string): void;
  wroteCopies(resource: string, map: string): void;
  wroteShown(resource: string, slot: string): void;
  transitionPart(part: number): void;
  microstepEnds(check: RegionCheck): void;
  readRecord(part: RecordPart): void;
  /** Reports a write of `part`. `keyWrite` is true when a created or deleted record writes the entity's key set. */
  wroteRecord(part: RecordPart, keyWrite: boolean): void;
  readContext(resource: string, field: string): void;
  wroteContext(resource: string, field: string): void;
  readShown(resource: string, slot: string): void;
  readNow(): void;
  wroteNow(): void;
  reached(obligation: Obligation): void;
  /**
   * Reports that chart or automation `sender` sent the request of `activity` while the requests of the `waiting`
   * activities awaited answers.
   */
  requested(activity: Activity, sender: string, waiting: readonly Activity[]): void;
  /** Reports that no entry of `deadlineOrder` was left for a tie among `deadlines`, so the first of them fires. */
  unchosenTie(deadlines: readonly DeadlineId[]): void;
}
