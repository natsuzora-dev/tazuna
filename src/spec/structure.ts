import { type DefinitionRef, sameRef } from "../data/definitionRef.ts";
import type { InvalidInput } from "../data/invalidInput.generated.ts";
import type { Mismatch } from "../data/mismatch.generated.ts";
import type { Answer, Rejection, RejectionKind } from "../data/trace.generated.ts";
import type { TransitionRef, Trigger } from "../data/transitionRef.generated.ts";
import type { Structure } from "./structure.generated.ts";

export type DefinitionStructure = Structure["definitions"][number];
export type ChartStructure = Extract<DefinitionStructure, { kind: "machine" | "screen" }>;
export type StateStructure = ChartStructure["states"][number];
export type TransitionStructure = StateStructure["transitions"][number];
export type ActivityStructure = StateStructure["activities"][number];
type CommandStructure = Extract<DefinitionStructure, { kind: "command" }>;

const kinds: { readonly [K in DefinitionStructure["kind"]]: K } = {
  entity: "entity",
  event: "event",
  command: "command",
  query: "query",
  automation: "automation",
  machine: "machine",
  screen: "screen",
};

export const definitionKinds = Object.values(kinds);

/**
 * Returns the trace name of `ref` as seen from `service`; a ref of another service gets its service name as a prefix.
 */
export const traceNameOfRef = (ref: DefinitionRef, service?: string): string =>
  ref.service === service ? ref.name : `${ref.service}.${ref.name}`;

/**
 * Returns the ref that a trace name as seen from `service` spells: the part before the last dot, if any, is the
 * service.
 */
export function refOfTraceName(service: string, traceName: string): DefinitionRef {
  const dot = traceName.lastIndexOf(".");
  return dot < 0 ? { service, name: traceName } : { service: traceName.slice(0, dot), name: traceName.slice(dot + 1) };
}

export const isAnswerTransition = (t: TransitionStructure): boolean =>
  t.trigger.type === "calls" || t.trigger.type === "sends" || t.trigger.type === "opens";

export const transitionRef = (t: {
  readonly source: string | null;
  readonly trigger: Trigger;
  readonly index: number;
}): TransitionRef => ({
  state: t.source,
  trigger: t.trigger,
  index: t.index,
});

export function chartStructure(structure: Structure, service: string, name: string): ChartStructure | undefined {
  return structure.definitions.find(
    (d): d is ChartStructure =>
      (d.kind === "machine" || d.kind === "screen") && d.service === service && d.name === name,
  );
}

export function stateNamed(chart: ChartStructure, name: string): StateStructure | undefined {
  return chart.states.find((s) => s.name === name);
}

export function isOpenedByScreen(structure: Structure, definition: DefinitionRef): boolean {
  return structure.definitions.some(
    (d) =>
      d.kind === "screen" &&
      Object.values(d.screens).some((s) => s?.service === definition.service && s.name === definition.name),
  );
}

/** Returns the definition with trace name `name` whose kind is one of `kinds`. */
export function named(
  structure: Structure,
  service: string,
  name: string | undefined,
  kinds: readonly DefinitionStructure["kind"][],
): DefinitionStructure | undefined {
  if (name === undefined) return undefined;
  return structure.definitions.find((d) => kinds.includes(d.kind) && traceNameOfRef(d, service) === name);
}

/** Returns the services whose contract lists `ref`. */
export function contractsListing(structure: Structure, ref: DefinitionRef): string[] {
  return structure.contracts
    .filter((c) => Object.values(c.members).some((member) => sameRef(member, ref)))
    .map((c) => c.service);
}

/**
 * Returns the kinds that an answer to the command or query `target` may be rejected with when a definition of `service`
 * sends it: for an external `target`, the kinds it declares. Otherwise `requires` needs a requires condition or a binds
 * value, `not-found` an input ref field, and `already-exists` an emitted event that creates or updates a record, and a
 * request to another service may also be rejected with `unavailable`, and a command to another service with
 * `reused-id`. An answer rejected with `invalid-input` is the sender's fault (inputFault), so it is not listed.
 */
export function rejectionKinds(structure: Structure, service: string, target: DefinitionRef): RejectionKind[] {
  const definition = structure.definitions.find((d) => sameRef(d, target));
  if (definition?.kind !== "command" && definition?.kind !== "query") return [];
  if (definition.rejects !== null) return definition.rejects;
  const other = <K extends RejectionKind>(kind: K): K[] => (target.service === service ? [] : [kind]);
  if (definition.kind === "query")
    return [...(definition.requires.length === 0 ? [] : ["requires" as const]), ...other("unavailable")];
  const writes = definition.emits.some((e) =>
    structure.definitions.some(
      (d) => d.kind === "event" && sameRef(d, e) && (d.change === "create" || d.change === "update"),
    ),
  );
  return [
    ...other("reused-id"),
    ...(definition.references.length === 0 ? [] : ["not-found" as const]),
    ...(definition.binds.length === 0 && definition.requires.length === 0 ? [] : ["requires" as const]),
    ...(writes ? ["already-exists" as const] : []),
    ...other("unavailable"),
  ];
}

/**
 * Returns the events that the command `command` lists in its emits, with null for an entry that names no definition.
 */
export function emitsOf(structure: Structure, command: DefinitionRef | null): readonly (DefinitionRef | null)[] {
  return (
    structure.definitions.find((d): d is CommandStructure => d.kind === "command" && sameRef(d, command))?.emits ?? []
  );
}

/** Returns the requires conditions of the command or query `target`. */
export function requiresOf(structure: Structure, target: DefinitionRef): string[] {
  const definition = structure.definitions.find((d) => sameRef(d, target));
  return definition?.kind === "command" || definition?.kind === "query" ? [...definition.requires] : [];
}

/**
 * Returns the reasons that a requires rejection of the command or query `target` may name: its binds, then its
 * requires.
 */
export function rejectionReasons(structure: Structure, target: DefinitionRef): string[] {
  const definition = structure.definitions.find((d) => sameRef(d, target));
  if (definition?.kind === "command") return [...definition.binds, ...definition.requires];
  if (definition?.kind === "query") return [...definition.requires];
  return [];
}

export function hasOutput(structure: Structure, target: DefinitionRef): boolean {
  const definition = structure.definitions.find((d) => sameRef(d, target));
  return (definition?.kind === "command" || definition?.kind === "query") && definition.output !== null;
}

/**
 * Returns whether an answer to the command or query `target` is checked against `target`'s assumed contract, which
 * holds when `target` is a command or query of an external service. test checks an answer from another service in the
 * same spec against that service's run instead (peerFindings).
 */
export function isAssumed(structure: Structure, target: DefinitionRef): boolean {
  const definition = structure.definitions.find((d) => sameRef(d, target));
  return (
    (definition?.kind === "command" || definition?.kind === "query") &&
    structure.services.find((s) => s.name === target.service)?.external === true
  );
}

/** Why an event cannot be the result (resultOf) of a request. */
export type ResultOfMismatch = "resultOfNonCommand" | "resultOfUnacceptedRequest" | "resultOfUnlistedEvent";

/**
 * Returns why `event` cannot be the result of a request to `target`, or undefined when it can. `event` can be the
 * result only when `target` is a command that accepted the request and lists `event` in its emits.
 */
export function resultOfMismatch(
  structure: Structure,
  target: DefinitionRef,
  accepted: boolean,
  event: DefinitionRef,
): ResultOfMismatch | undefined {
  const definition = structure.definitions.find((d) => sameRef(d, target));
  if (definition?.kind !== "command") return "resultOfNonCommand";
  if (!accepted) return "resultOfUnacceptedRequest";
  return definition.emits.some((e) => sameRef(e, event)) ? undefined : "resultOfUnlistedEvent";
}

/** Lean's AssumptionMismatch: what an answer to a request, or its result events, break of the target's contract. */
export type AssumptionMismatch =
  | { readonly kind: "unlistedRejectionKind"; readonly rejection: Rejection }
  | { readonly kind: "answerOutputSchema" }
  | { readonly kind: "rejectedAssumedRequires" }
  | { readonly kind: "failedAssumedRequires"; readonly condition: string }
  | { readonly kind: "failedAssumedEnsures"; readonly condition: string };

type Assumed<V extends { readonly kind: string }, G extends string> = Extract<
  V,
  { readonly kind: `${G}.${AssumptionMismatch["kind"]}` }
>;

interface RequestRef {
  readonly requestId: string;
  readonly target: DefinitionRef;
}

/**
 * Lean's `assumption` constructor of InvalidInput and Mismatch, which derive_group flattens: the violation of `group`
 * that `m` names for the answer to `request`.
 */
export function assumptionViolation(
  group: "InvalidInput",
  request: RequestRef,
  m: AssumptionMismatch,
): Assumed<InvalidInput, "InvalidInput">;
export function assumptionViolation(
  group: "Mismatch",
  request: RequestRef,
  m: AssumptionMismatch,
  line: number,
): Assumed<Mismatch, "Mismatch">;
export function assumptionViolation(group: string, request: RequestRef, m: AssumptionMismatch, line?: number): unknown {
  const { kind, ...data } = m;
  return {
    kind: `${group}.${kind}`,
    definition: null,
    ...(line === undefined ? {} : { line }),
    data: { ...request, ...data },
  };
}

/**
 * Returns the assumption that an answer breaks, given the first assumed requires that fails and, when the requires hold
 * and the answer is not a rejection, the first assumed ensures that fails. A broken requires promises no ensures.
 */
export function assumptionMismatch(
  answer: Answer,
  failedRequires: string | undefined,
  failedEnsures: string | undefined,
): AssumptionMismatch | undefined {
  if (answer.result === "rejected")
    return answer.rejection.kind === "requires" && failedRequires === undefined
      ? { kind: "rejectedAssumedRequires" }
      : undefined;
  if (failedRequires !== undefined) return { kind: "failedAssumedRequires", condition: failedRequires };
  return failedEnsures === undefined ? undefined : { kind: "failedAssumedEnsures", condition: failedEnsures };
}

export function schemaProperties(schema: unknown): string[] {
  const properties = (schema as { readonly properties?: unknown } | null)?.properties;
  return properties !== null && typeof properties === "object" ? Object.keys(properties) : [];
}

/** Lean's isKeyOf: whether `value` has the form `<entity>-<n>` of the `n`-th createKey value of the entity. */
export function isKeyOf(entity: string, value: string): boolean {
  return value.startsWith(`${entity}-`) && /^[1-9][0-9]*$/.test(value.slice(entity.length + 1));
}
