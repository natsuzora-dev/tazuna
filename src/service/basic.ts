import { sortCollections } from "../data/collections.ts";
import { type DefinitionRef, sameRef } from "../data/definitionRef.ts";
import { expectFound } from "../data/internalError.ts";
import type { Activity } from "../data/step.generated.ts";
import type { Json } from "../data/values.ts";
import type { KeyPosition, Structure } from "../spec/structure.generated.ts";
import { type DefinitionStructure, isOpenedByScreen, mapStateOf, schemaProperties } from "../spec/structure.ts";
import { type Chart, executableChart } from "./chart/basic.ts";

type Change =
  | { readonly kind: "none" }
  /** `key` is the payload field that holds the entity key. */
  | { readonly kind: "create"; readonly entity: string; readonly key: string; readonly fields: readonly string[] }
  /** Overwrites `writes` of the keyed record, or creates the record from the payload if it is missing. */
  | { readonly kind: "update"; readonly entity: string; readonly key: string; readonly writes: readonly string[] }
  | { readonly kind: "delete"; readonly entity: string; readonly key: string; readonly fields: readonly string[] }
  | { readonly kind: "set"; readonly entity: string; readonly writes: readonly string[] };

/** What a command or query checks before processing, in declaration order. */
interface Requirements {
  /** The input ref fields and the entity that each points to. */
  readonly refs: readonly (readonly [string, DefinitionRef])[];
  readonly binds: readonly string[];
  readonly requires: readonly string[];
}

export interface Automation {
  readonly name: string;
  /** The rank among the spec's definitions. */
  readonly order: number;
  readonly receives: DefinitionRef;
  readonly sends: Activity;
  readonly binds: readonly string[];
  readonly guard: readonly string[];
}

/**
 * A schema that values are checked against. `mapContext` is the copy context of the map state `map`, and `record` the
 * fields of the entity `entity`.
 */
export type Schema =
  | { readonly kind: "input"; readonly definition: DefinitionRef }
  | { readonly kind: "payload"; readonly event: DefinitionRef }
  | { readonly kind: "output"; readonly definition: DefinitionRef }
  | { readonly kind: "control"; readonly screen: DefinitionRef; readonly control: string }
  | { readonly kind: "held"; readonly chart: DefinitionRef; readonly state: string }
  | { readonly kind: "context"; readonly chart: DefinitionRef }
  | { readonly kind: "mapContext"; readonly chart: DefinitionRef; readonly map: string }
  | { readonly kind: "mapKey"; readonly chart: DefinitionRef; readonly map: string }
  | { readonly kind: "record"; readonly entity: DefinitionRef };

/**
 * The values of one service read from the structure. The lists that Lean looks up by name are maps.
 */
export interface Service {
  readonly service: string;
  readonly structure: Structure;
  readonly commands: readonly string[];
  readonly queries: readonly string[];
  /** The own events and how each changes records. */
  readonly events: ReadonlyMap<string, Change>;
  /**
   * The events of other services' contracts that the service's definitions receive: an automation's or a chart's
   * event, or a result event of a command that an automation or a chart sends. A simulation delivers an event only to
   * the services that receive it.
   */
  readonly receives: readonly DefinitionRef[];
  /** The automations in definition order. */
  readonly automations: readonly Automation[];
  /** The machines and screens, in definition order. */
  readonly charts: ReadonlyMap<string, Chart>;
  /** The own entities, in the order of the service's `entities`. */
  readonly entities: readonly string[];
  readonly singles: readonly string[];
  /** The `ref()` fields and the entity that each references, in entity and then field order. */
  readonly references: readonly { readonly entity: string; readonly field: string; readonly target: string }[];
  readonly uniques: ReadonlyMap<string, readonly string[]>;
  /** The key positions of each own entity's records, in the order of `entities`. */
  readonly recordKeys: readonly (readonly [string, readonly KeyPosition[]])[];
  readonly requirements: ReadonlyMap<string, Requirements>;
}

export const ref = (st: Service, name: string): DefinitionRef => ({ service: st.service, name });

/** Lean's Service.changeOf: how the event `r` changes records, when it is an own event. */
export const changeOf = (st: Service, r: DefinitionRef): Change | undefined =>
  r.service === st.service ? st.events.get(r.name) : undefined;

export function schemaOwner(schema: Schema): DefinitionRef {
  switch (schema.kind) {
    case "input":
    case "output":
      return schema.definition;
    case "payload":
      return schema.event;
    case "control":
      return schema.screen;
    case "held":
    case "context":
    case "mapContext":
    case "mapKey":
      return schema.chart;
    case "record":
      return schema.entity;
  }
}

/**
 * Lean's Service.schemaOf: the JSON Schema that `schema` names, read from the structure. The loader builds every schema that a run names, so a missing one is an InternalError.
 */
export function schemaOf(st: Service, schema: Schema): unknown {
  const body = (r: DefinitionRef) => st.structure.definitions.find((d) => sameRef(d, r));
  const state = (chart: DefinitionRef, name: string) => {
    const d = body(chart);
    return d?.kind === "machine" || d?.kind === "screen" ? d.states.find((s) => s.name === name) : undefined;
  };
  const found = ((): unknown => {
    switch (schema.kind) {
      case "input":
      case "output": {
        const d = body(schema.definition);
        if (d?.kind === "command" || d?.kind === "query") return d[schema.kind] ?? undefined;
        return d?.kind === "machine" || d?.kind === "screen" ? d[schema.kind] : undefined;
      }
      case "payload": {
        const d = body(schema.event);
        return d?.kind === "event" ? d.payload : undefined;
      }
      case "control": {
        const d = body(schema.screen);
        if (d?.kind !== "screen" || !Object.hasOwn(d.controls, schema.control)) return undefined;
        return d.controls[schema.control] ?? {};
      }
      case "held":
        return state(schema.chart, schema.state)?.held?.schema;
      case "context": {
        const d = body(schema.chart);
        return d?.kind === "machine" || d?.kind === "screen" ? d.context : undefined;
      }
      case "mapContext":
        return mapStateOf(state(schema.chart, schema.map))?.context;
      case "mapKey":
        return mapStateOf(state(schema.chart, schema.map))?.key;
      case "record": {
        const d = body(schema.entity);
        return d?.kind === "entity" ? d.fields : undefined;
      }
    }
  })();
  return expectFound(`schema ${JSON.stringify(schema)}`, found);
}

/** Lean's Service.sorted: an encoded value with its collections sorted by the structure's schema. */
export const sorted = (st: Service, schema: Schema, json: Json): Json => sortCollections(schemaOf(st, schema), json);

export const uniqueOf = (st: Service, entity: string): readonly string[] => st.uniques.get(entity) ?? [];

type EntityStructure = Extract<DefinitionStructure, { kind: "entity" }>;

/**
 * Lean's ofStructure: the service `service` of the structure. An entity that an event changes or the service lists is
 * guaranteed by the loader (Malformed.unresolvedReference), so a lookup that finds none is an InternalError.
 */
export function serviceOf(structure: Structure, service: string): Service {
  const own = structure.definitions.map((d, order) => ({ d, order })).filter(({ d }) => d.service === service);
  const entityBody = (r: DefinitionRef): EntityStructure =>
    expectFound(
      `entity ${r.service}.${r.name}`,
      structure.definitions.find((d): d is EntityStructure => d.kind === "entity" && sameRef(d, r)),
    );
  const keyed = (r: DefinitionRef) => {
    const body = entityBody(r);
    return {
      key: expectFound(`key of the entity ${r.name}`, body.key ?? undefined),
      fields: schemaProperties(body.fields),
    };
  };
  const charts = new Map<string, Chart>();
  const commands: string[] = [];
  const queries: string[] = [];
  const events = new Map<string, Change>();
  const automations: Automation[] = [];
  for (const { d, order } of own) {
    const { name } = d;
    switch (d.kind) {
      case "machine":
      case "screen": {
        const opened = d.kind === "screen" && isOpenedByScreen(structure, d);
        charts.set(name, executableChart(d, order, opened));
        break;
      }
      case "event": {
        const { change } = d;
        if (change === null) {
          events.set(name, { kind: "none" });
          break;
        }
        const entity = change.entity.name;
        if (change.kind === "update") {
          const { key } = entityBody(change.entity);
          events.set(
            name,
            key === null
              ? { kind: "set", entity, writes: schemaProperties(d.payload) }
              : { kind: "update", entity, key, writes: schemaProperties(d.payload).filter((f) => f !== key) },
          );
          break;
        }
        events.set(name, { kind: change.kind, entity, ...keyed(change.entity) });
        break;
      }
      case "command":
        commands.push(name);
        break;
      case "query":
        queries.push(name);
        break;
      case "automation": {
        const sends: Activity = { keyword: "sends", key: name, target: d.command };
        automations.push({ name, order, receives: d.receives, sends, binds: d.binds, guard: d.guard });
        break;
      }
      default:
        break;
    }
  }
  const listed = structure.contracts
    .filter((c) => c.service !== service)
    .flatMap((c) =>
      Object.values(c.members).flatMap((r) =>
        r !== null && structure.definitions.some((d) => d.kind === "event" && sameRef(d, r)) ? [r] : [],
      ),
    );
  const heard = own.flatMap(({ d }) =>
    d.kind === "automation"
      ? [d.receives]
      : d.kind === "machine" || d.kind === "screen"
        ? Object.values(d.receives)
        : [],
  );
  const sent = own.flatMap(({ d }) =>
    d.kind === "automation"
      ? [d.command]
      : d.kind === "machine" || d.kind === "screen"
        ? Object.values(d.commands)
        : [],
  );
  const results = structure.definitions.flatMap((d) =>
    d.kind === "command" && sent.some((c) => sameRef(c, d)) ? d.emits : [],
  );
  const receives = listed.filter((n) => [...heard, ...results].some((r) => sameRef(r, n)));
  const entities = expectFound(
    `service ${service}`,
    structure.services.find((s) => s.name === service),
  ).entities;
  const bodies = entities.map((e) => [e, entityBody({ service, name: e })] as const);
  return {
    service,
    structure,
    commands,
    queries,
    events,
    receives,
    automations,
    charts,
    entities,
    singles: bodies.flatMap(([e, b]) => (b.key === null ? [e] : [])),
    references: bodies.flatMap(([e, b]) =>
      b.references.map((r) => ({ entity: e, field: r.field, target: r.entity.name })),
    ),
    uniques: new Map(bodies.map(([e, b]) => [e, b.unique])),
    recordKeys: bodies.map(([e, b]) => [e, b.keys] as const),
    requirements: requirementsOf(structure, service),
  };
}

/** Lean's requirementsOf: the requirements of each own command, query, and screen of `service`. */
function requirementsOf(structure: Structure, service: string): ReadonlyMap<string, Requirements> {
  return new Map(
    structure.definitions.flatMap((d): [string, Requirements][] => {
      if (d.service !== service) return [];
      if (d.kind === "command")
        return [
          [
            d.name,
            {
              refs: d.references.map(({ field, entity }) => [field, entity] as const),
              binds: d.binds,
              requires: d.requires,
            },
          ],
        ];
      if (d.kind === "query" || d.kind === "screen") return [[d.name, { refs: [], binds: [], requires: d.requires }]];
      return [];
    }),
  );
}
