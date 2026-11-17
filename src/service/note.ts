import type { DefinitionRef } from "../data/definitionRef.ts";
import type { StepName } from "../data/step.generated.ts";
import type { TransitionRef } from "../data/transitionRef.generated.ts";
import type { Obligation } from "../data/uncovered.ts";
import { canonicalJson, type Json } from "../data/values.ts";
import { chartOf, type InstanceId, instanceName } from "./instance.ts";

/**
 * A part of the records: the entity's key set when there is no key and no field, the record's existence when there is
 * a key only, and the field's value when there is a field.
 */
export interface RecordPart {
  readonly entity: string;
  readonly key?: string;
  readonly field?: string;
}

/** Lean's Channel: the channel that an `out` line travels on, seen from its sender (channelOf). */
export type Channel =
  | { readonly kind: "request"; readonly id: string }
  | { readonly kind: "answers"; readonly request: string }
  | { readonly kind: "events"; readonly resultOf: string | null };

export function sameChannel(a: Channel, b: Channel): boolean {
  switch (a.kind) {
    case "request":
      return b.kind === "request" && b.id === a.id;
    case "answers":
      return b.kind === "answers" && b.request === a.request;
    case "events":
      return b.kind === "events" && b.resultOf === a.resultOf;
  }
}

/**
 * Lean's ValueKey: a value that steps read and write. Being in a state also stands for the copy set of a map state, and
 * a channel for the order of the lines on it.
 */
export type ValueKey =
  | { readonly kind: "record"; readonly part: RecordPart }
  | { readonly kind: "context"; readonly id: InstanceId; readonly field: string }
  | { readonly kind: "state"; readonly id: InstanceId; readonly state: string }
  | { readonly kind: "shown"; readonly id: InstanceId; readonly slot: string }
  | { readonly kind: "channel"; readonly channel: Channel };

/** The one string form of a key, which the footprints' sets and the evaluation cache hold. It is a JSON array. */
export function valueName(k: ValueKey): string {
  switch (k.kind) {
    case "record":
      return JSON.stringify(["record", k.part.entity, k.part.key ?? null, k.part.field ?? null]);
    case "context":
      return `["context",${instanceName(k.id)},${JSON.stringify(k.field)}]`;
    case "state":
      return `["state",${instanceName(k.id)},${JSON.stringify(k.state)}]`;
    case "shown":
      return `["shown",${instanceName(k.id)},${JSON.stringify(k.slot)}]`;
    case "channel":
      return JSON.stringify(["channel", k.channel]);
  }
}

/** The key of a step name. The search takes steps with equal names as one, so equal names must run equal work. */
const stepKey = (name: StepName): string => canonicalJson(name as Json);

export const sameStep = (a: StepName, b: StepName): boolean => stepKey(a) === stepKey(b);

/** The key of a sequence of steps. */
export const stepsKey = (names: readonly StepName[]): string => names.map(stepKey).join("\n");

/** Lean's StepName.definition: the definition of the step, in service `service`. */
export function stepNameDefinition(service: string, name: StepName): DefinitionRef {
  switch (name.kind) {
    case "reaction":
      return { service, name: name.automation };
    case "command":
    case "answer":
      return {
        service,
        name: name.sender.kind === "automation" ? name.sender.automation : chartOf(name.sender.machine),
      };
    default:
      return { service, name: chartOf(name.id) };
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
 * - reached is TS only: the coverage hits that explore reads.
 */
export interface Note {
  /** Reports that step `step` wrote event lines from line `start` in groups of the lengths `groups`. */
  events(step: number, start: number, groups: readonly number[]): void;
  stepBegins(step: number, name: StepName, started: InstanceId | undefined): void;
  stepEnds(): void;
  /**
   * Reports that the open step evaluates the always transitions of `owner` and its copies before and after its work.
   */
  settlesAround(owner: InstanceId): void;
  /** Reports that the open step read whether instances or copies are in states. */
  readStates(states: readonly (readonly [InstanceId, string])[]): void;
  wroteState(id: InstanceId, state: string): void;
  wroteCopies(id: InstanceId, map: string): void;
  wroteShown(id: InstanceId, slot: string): void;
  transitionPart(part: number): void;
  microstepEnds(check: RegionCheck): void;
  /** Reports the start of the checks and subscription answers after message `message`, which no step runs. */
  afterMessageBegins(message: number): void;
  afterMessageEnds(): void;
  readRecord(part: RecordPart): void;
  /** Reports a write of `part`. `keyWrite` is true when a created or deleted record writes the entity's key set. */
  wroteRecord(part: RecordPart, keyWrite: boolean): void;
  readContext(id: InstanceId, field: string): void;
  wroteContext(id: InstanceId, field: string): void;
  readShown(id: InstanceId, slot: string): void;
  readNow(): void;
  wroteNow(): void;
  reached(obligation: Obligation): void;
}
