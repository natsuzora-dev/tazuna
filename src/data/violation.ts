import type { z } from "zod";
import type { DefinitionRef } from "./definitionRef.ts";
import type { Line } from "./scenario.generated.ts";
import { type Json, plain } from "./values.ts";

export type Data = Readonly<Record<string, Json>>;

export type ViolationValue = {
  readonly kind: Kind;
  readonly definition: DefinitionRef | null;
  readonly data: Data;
};

/**
 * The place that a violation names beside its data, as Lean's derive_group writes it: the scenario and the line of the
 * compared file. A report moves them to `scenario` and `location`.
 */
export interface Placed {
  readonly scenario?: DefinitionRef;
  readonly line?: number;
}

/** The fields that only TS reports beside a violation's kind, definition, and data. */
export interface Located {
  readonly error?: ViolationError;
  readonly location?: Location;
}

/**
 * Lean's Violation, with the fields that only TS reports. `definition` is the cause, or null when the subject is not a
 * definition.
 */
export interface Violation extends ViolationValue, Located {}

/** Returns `value` with the fields that only TS reports; an undefined field is left out. */
export function withExtra<V>(value: V, extra: { readonly [K in keyof Located]?: Located[K] | undefined }): V & Located {
  return {
    ...value,
    ...(extra.error === undefined ? {} : { error: extra.error }),
    ...(extra.location === undefined ? {} : { location: extra.location }),
  };
}

/** A violation's group: the part of its kind before the dot. */
export type Group =
  | "Malformed"
  | "Illegal"
  | "NonCanonical"
  | "Restricted"
  | "InvalidInput"
  | "Fault"
  | "BagOrderDependent"
  | "ChoiceDependent"
  | "Undecided"
  | "Mismatch"
  | "Uncomparable"
  | "Uncovered"
  | "InvalidScenario";

export type Kind = `${Group}.${string}`;

/**
 * The location of a violation. `file` is relative to the spec folder. Without `line`, the location is a whole file or a
 * folder entry.
 */
export interface Location {
  readonly file: string;
  readonly line?: number;
}

/** The value that a spec function threw, or the reason that Zod rejected a value. */
export type ViolationError =
  | { readonly type: "thrownError"; readonly name: string; readonly message: string; readonly stack?: string }
  | { readonly type: "thrownValue"; readonly value: Json }
  | { readonly type: "zod"; readonly issues: readonly z.core.$ZodIssue[] };

/** Returns `value` as JSON, or as its string when JSON.stringify throws on a bigint or a cycle. */
function thrownJson(value: unknown): Json {
  try {
    return plain(value);
  } catch {
    return String(value);
  }
}

export function thrown(value: unknown): ViolationError {
  if (!(value instanceof Error)) return { type: "thrownValue", value: thrownJson(value) };
  const { name, message, stack } = value;
  return { type: "thrownError", name, message, ...(stack === undefined ? {} : { stack }) };
}

export const zodError = (issues: readonly z.core.$ZodIssue[]): ViolationError => ({ type: "zod", issues });

/**
 * A reported violation, with its location. `scenario` is the scenario that the violation is about, and `appendedLines`
 * the lines appended to it before the violation.
 */
export interface ReportedViolation extends ViolationValue {
  readonly location: Location;
  readonly scenario?: DefinitionRef;
  readonly appendedLines?: readonly Line[];
  readonly error?: ViolationError;
}

/**
 * Returns the violation as a ReportedViolation at `at`, with the scenario and the line that the violation names itself in its
 * place.
 */
export function toReported(
  v: ViolationValue & Placed & Pick<ReportedViolation, "error">,
  at: Location,
  extra: Pick<ReportedViolation, "scenario" | "appendedLines"> = {},
): ReportedViolation {
  const line = v.line ?? at.line;
  const scenario = v.scenario ?? extra.scenario;
  return {
    kind: v.kind,
    definition: v.definition,
    data: v.data,
    location: { file: at.file, ...(line === undefined ? {} : { line }) },
    ...(scenario === undefined ? {} : { scenario }),
    ...(extra.appendedLines === undefined ? {} : { appendedLines: extra.appendedLines }),
    ...(v.error === undefined ? {} : { error: v.error }),
  };
}
