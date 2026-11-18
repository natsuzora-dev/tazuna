import type { DefinitionRef } from "../data/definitionRef.ts";
import { haltingFaultKinds } from "../data/fault.generated.ts";
import { haltingInvalidInputKinds } from "../data/invalidInput.generated.ts";
import { type Answer, byCallerKinds, type LineId, type RejectionKind } from "../data/trace.generated.ts";
import type { Fields, Json } from "../data/values.ts";
import type { Kind } from "../data/violation.ts";

/** Lean's RejectionKind.byCaller. */
export const byCaller: ReadonlySet<RejectionKind> = new Set(byCallerKinds);

/** The kinds whose violations halt the run. */
export type Halting = (typeof haltingFaultKinds)[number] | (typeof haltingInvalidInputKinds)[number];

const halting: ReadonlySet<Kind> = new Set<Kind>([...haltingFaultKinds, ...haltingInvalidInputKinds]);

/** Lean's Finding.halts. */
export const halts = (kind: Kind): boolean => halting.has(kind);

/** An emitted event, with `payload` decoded. */
export interface Emit {
  readonly event: DefinitionRef;
  readonly payload: Fields;
}

/** An emitted event that a service took, with `encoded`, the payload as Lean's Emit holds it, which names its steps. */
export interface Emitted extends Emit {
  readonly encoded: Json;
}

/** Lean's LineBody: what a line of a run carries. `operation` writes `payload` only when its control has fields. */
export type LineBody =
  | { readonly type: "command" | "query" | "subscribe"; readonly target: DefinitionRef; readonly input: unknown }
  | { readonly type: "event"; readonly event: DefinitionRef; readonly payload: unknown; readonly resultOf?: LineId }
  | { readonly type: "answer"; readonly to: LineId; readonly answer: Answer }
  | { readonly type: "unsubscribe"; readonly to: LineId }
  | { readonly type: "time" | "restart" }
  | {
      readonly type: "operation";
      readonly screen: DefinitionRef;
      readonly control: string;
      readonly nth?: number;
      readonly payload?: unknown;
    };

/** Lean's LineBody.content: a request's input, an event's or operation's payload, an answer. */
export function bodyContent(b: LineBody): unknown {
  switch (b.type) {
    case "command":
    case "query":
    case "subscribe":
      return b.input;
    case "event":
    case "operation":
      return b.payload;
    case "answer":
      return b.answer;
    default:
      return undefined;
  }
}

/** Lean's EmittedBy: the step that wrote an event line, and the place of its group among the groups of the decide. */
export interface EmittedBy {
  readonly step: number;
  readonly group: number;
}

/** Lean's Line: a line of a run, which traceLineOf turns into a trace line. */
export type Line = LineBody & {
  readonly time: string;
  readonly dir: "in" | "out";
  readonly id: LineId;
  readonly emitted?: EmittedBy;
  /** Set on the `out` request lines: the definition of the service that sent the request. */
  readonly sender?: string;
};

/** The key of a line id in a map, as Lean compares line ids. */
export const idKey = (id: LineId): string => JSON.stringify(id.kind === "own" ? [id.id] : [id.sender, id.id]);

export const sameLineId = (a: LineId | undefined, b: LineId | undefined): boolean =>
  a === undefined || b === undefined ? a === b : idKey(a) === idKey(b);
