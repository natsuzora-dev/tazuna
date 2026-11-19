import type { DefinitionRef } from "../data/definitionRef.ts";
import type { TraceLine } from "../data/trace.generated.ts";
import type { MalformedLine } from "../data/trace.ts";
import type { Trigger } from "../data/transitionRef.generated.ts";
import type { Json } from "../data/values.ts";
import type { ActivityStructure, DefinitionStructure, StateStructure, TransitionStructure } from "../spec/structure.ts";

/** The model that the server serves to the viewer as /model.json. */
export interface ViewModel {
  readonly spec: string;
  readonly services: readonly ServiceView[];
  readonly scenarios: readonly ScenarioView[];
}

export interface ServiceView {
  /** `external` for a service defined with externalService(), and `screens` for a service that has screens. */
  readonly kind: "service" | "external" | "screens";
  readonly name: string;
  readonly description: string;
  /** The services whose contract.ts this service's files import. */
  readonly uses: readonly string[];
  readonly invariants: Json;
  readonly definitions: readonly DefinitionView[];
}

export interface DefinitionView {
  readonly kind: DefinitionStructure["kind"];
  readonly name: string;
  /**
   * The definition as JSON: a Zod schema becomes JSON Schema, a function its source, a reference to another definition
   * `{ kind, service, name }`, a service its name, and undefined null.
   */
  readonly definition: Json;
  /** The chart of a machine or screen, or null for other kinds. */
  readonly chart: StateView | null;
  /** The entity of an entity definition, or null for other kinds. */
  readonly entity: EntityView | null;
}

/** An entity. `key` is null for a single entity. */
export interface EntityView extends Pick<Extract<DefinitionStructure, { kind: "entity" }>, "key" | "unique"> {
  readonly invariants: readonly string[];
  readonly fields: readonly FieldView[];
}

export interface FieldView {
  readonly name: string;
  /**
   * The type text from JSON Schema: a format by its name (date-time as datetime), enum, int, an array as its element
   * type plus [], and anyOf and oneOf as union. Null is left out and shows in `nullable`.
   */
  readonly type: string;
  readonly nullable: boolean;
  readonly description: string | null;
  /** The entity that a ref() field points to. */
  readonly ref: DefinitionRef | null;
}

/**
 * A state of a chart. The root has the definition's name, kind compound, and the chart's top-level `on` transitions.
 */
export interface StateView
  extends Omit<StateStructure, "children" | "activities" | "transitions" | "itemKeys" | "contextKeys"> {
  readonly activities: readonly ActivityView[];
  readonly transitions: readonly TransitionView[];
  readonly states: readonly StateView[];
}

/** An activity whose `kind` is what it requests or opens. */
export type ActivityView = ActivityStructure & { readonly kind: "query" | "command" | "screen" };

/**
 * A transition. `control` is whether its trigger is an `on` key that names a control of the chart. `path` is the keys
 * under which its state writes its transition array.
 */
export type TransitionView = TransitionStructure & {
  readonly id: string;
  readonly control: boolean;
  readonly path: readonly string[];
};

export type { Trigger };

export interface ScenarioView {
  readonly service: string;
  readonly name: string;
  readonly description: string;
  /** The snapshot, or null without a snapshot or when a snapshot line fails the trace schema. */
  readonly trace: readonly TraceLine[] | null;
  /** The first snapshot line that fails the trace schema. */
  readonly error: MalformedLine | null;
  /** The scenario's service, then the others in the order of their first request in the trace. */
  readonly lifelines: readonly string[];
  readonly entries: readonly FlowEntry[];
}

/**
 * An entry of a scenario flow. A null `from` or `to` is the scenario lifeline, and an event that a service emits has
 * the service as both.
 */
export type FlowEntry =
  | { readonly type: "time"; readonly line: number }
  | { readonly type: "message"; readonly line: number; readonly from: string | null; readonly to: string | null };

/** An event sent on /events. `error` means that the spec failed to load and model.json is unchanged. */
export type ViewEvent = { readonly type: "model" } | { readonly type: "error"; readonly message: string };
