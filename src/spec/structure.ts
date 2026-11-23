import type { DefinitionRef } from "../data/definitionRef.ts";
import type { TransitionRef, Trigger } from "../data/transitionRef.generated.ts";
import type { Program } from "./ir.generated.ts";
import type {
  Activity as ActivityStructure,
  Definition as DefinitionStructure,
  State as StateStructure,
  Structure,
  Transition as TransitionStructure,
} from "./structure.generated.ts";

export type { ActivityStructure, DefinitionStructure, StateStructure, TransitionStructure };
export type ChartStructure = Extract<DefinitionStructure, { kind: "machine" | "screen" }>;

/** The program of a loaded spec, empty until check converts the spec functions to IR. */
export const unconverted: Program = {
  inputRequirement: [],
  resultEnsures: [],
  invariant: [],
  closeEnsures: [],
  binding: [],
  requirement: [],
  ensures: [],
  queryEnsures: [],
  serviceInvariant: [],
  automationBinding: [],
  automationGuard: [],
  resolve: [],
  decide: [],
  react: [],
  chart: [],
};

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

/** Lean's isKeyOf: whether `value` has the form `<entity>-<n>` of the `n`-th createKey value of the entity. */
export function isKeyOf(entity: string, value: string): boolean {
  return value.startsWith(`${entity}-`) && /^[1-9][0-9]*$/.test(value.slice(entity.length + 1));
}
