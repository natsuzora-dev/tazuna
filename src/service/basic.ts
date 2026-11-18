import { type DefinitionRef, sameRef } from "../data/definitionRef.ts";
import type { Activity } from "../data/step.generated.ts";
import type { Structure } from "../spec/structure.generated.ts";
import { isOpenedByScreen, schemaProperties } from "../spec/structure.ts";
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
export interface Requirements {
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
  | { readonly kind: "held"; readonly chart: DefinitionRef; readonly state: string; readonly name: string }
  | { readonly kind: "context"; readonly chart: DefinitionRef }
  | { readonly kind: "mapContext"; readonly chart: DefinitionRef; readonly map: string }
  | { readonly kind: "mapKey"; readonly chart: DefinitionRef; readonly map: string }
  | { readonly kind: "record"; readonly entity: DefinitionRef };

/**
 * The values of one service read from the structure. Lean's `schemas` has no field: the TS Functions check and sort
 * values themselves. The lists that Lean looks up by name are maps.
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

export const uniqueOf = (st: Service, entity: string): readonly string[] => st.uniques.get(entity) ?? [];

export const requirementsOf = (st: Service, name: string): Requirements =>
  st.requirements.get(name) ?? { refs: [], binds: [], requires: [] };

/**
 * Returns the service `service` of the structure. An automation without its event or command adds nothing, and an
 * event that changes records of no entity changes none.
 */
export function serviceOf(structure: Structure, service: string): Service {
  const own = structure.definitions.map((d, order) => ({ d, order })).filter(({ d }) => d.service === service);
  const entity = (r: DefinitionRef) => {
    const found = structure.definitions.find((d) => d.kind === "entity" && sameRef(d, r));
    return found?.kind === "entity" ? found : undefined;
  };
  const charts = new Map<string, Chart>();
  const commands: string[] = [];
  const queries: string[] = [];
  const events = new Map<string, Change>();
  const automations: Automation[] = [];
  const requirements = new Map<string, Requirements>();
  for (const { d, order } of own) {
    const { name } = d;
    switch (d.kind) {
      case "machine":
      case "screen": {
        const opened = d.kind === "screen" && isOpenedByScreen(structure, d);
        charts.set(name, executableChart(d, order, opened));
        if (d.kind === "screen") requirements.set(name, { refs: [], binds: [], requires: d.requires });
        break;
      }
      case "event": {
        const e = d.entity === null ? undefined : entity(d.entity);
        if (d.change === "none" || e === undefined) events.set(name, { kind: "none" });
        else if (d.change === "update")
          events.set(
            name,
            e.key === null
              ? { kind: "set", entity: e.name, writes: schemaProperties(d.payload) }
              : {
                  kind: "update",
                  entity: e.name,
                  key: e.key,
                  writes: schemaProperties(d.payload).filter((f) => f !== e.key),
                },
          );
        else if (e.key === null) events.set(name, { kind: "none" });
        else events.set(name, { kind: d.change, entity: e.name, key: e.key, fields: e.fields });
        break;
      }
      case "command":
        commands.push(name);
        requirements.set(name, {
          refs: d.references.flatMap((r) => (r.entity === null ? [] : [[r.field, r.entity] as const])),
          binds: d.binds,
          requires: d.requires,
        });
        break;
      case "query":
        queries.push(name);
        requirements.set(name, { refs: [], binds: [], requires: d.requires });
        break;
      case "automation": {
        const { receives, command } = d;
        if (receives === null || command === null) break;
        const sends: Activity = { keyword: "sends", key: name, target: command };
        automations.push({ name, order, receives, sends });
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
  const refs = (m: Readonly<Record<string, DefinitionRef | null>>) =>
    Object.values(m).flatMap((r) => (r === null ? [] : [r]));
  const heard = own.flatMap(({ d }) =>
    d.kind === "automation"
      ? d.receives === null
        ? []
        : [d.receives]
      : d.kind === "machine" || d.kind === "screen"
        ? refs(d.receives)
        : [],
  );
  const sent = own.flatMap(({ d }) =>
    d.kind === "automation"
      ? d.command === null
        ? []
        : [d.command]
      : d.kind === "machine" || d.kind === "screen"
        ? refs(d.commands)
        : [],
  );
  const results = structure.definitions.flatMap((d) =>
    d.kind === "command" && sent.some((c) => sameRef(c, d)) ? d.emits.flatMap((e) => (e === null ? [] : [e])) : [],
  );
  const receives = listed.filter((n) => [...heard, ...results].some((r) => sameRef(r, n)));
  const entities = structure.services.find((s) => s.name === service)?.entities ?? [];
  const ownEntity = (e: string) => entity({ service, name: e });
  const references = entities.flatMap((e) =>
    (ownEntity(e)?.references ?? []).flatMap((r) =>
      r.entity === null ? [] : [{ entity: e, field: r.field, target: r.entity.name }],
    ),
  );
  const uniques = new Map(
    entities.flatMap((e) => {
      const found = ownEntity(e);
      return found === undefined ? [] : [[e, found.unique] as const];
    }),
  );
  const singles = entities.filter((e) => ownEntity(e)?.key === null);
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
    singles,
    references,
    uniques,
    requirements,
  };
}
