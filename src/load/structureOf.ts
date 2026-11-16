import type { DefinitionRef } from "../data/definitionRef.ts";
import { type JsonSchema, objectSchema } from "../data/jsonSchema.ts";
import type { Shape } from "../data/values.ts";
import { chartOf, transitionArrays } from "../dsl/chart.ts";
import {
  any,
  type ChartSpec,
  type Contract,
  type Definition,
  type Named,
  type Services,
  type StateSpec,
} from "../dsl/definition.ts";
import { refTarget } from "../dsl/entity.ts";
import type { Structure } from "../syntax/structure.generated.ts";

import type {
  ActivityStructure,
  ChartStructure,
  DefinitionStructure,
  StateStructure,
  TransitionStructure,
} from "../syntax/structure.ts";

type RefOf = (value: unknown) => DefinitionRef | null;

/** The value that a default function threw while a schema that `definition` declares was converted to JSON Schema. */
export interface ThrownDefault {
  readonly definition: Definition;
  readonly error: unknown;
}

/**
 * Computes state trees and definition refs, which every other part reads from this JSON. A
 * schema whose conversion throws is {} in the structure; check stops at the Malformed.defaultSchema that the throw
 * becomes, before anything reads it.
 */
export function structureOf(
  definitions: readonly Named<Definition>[],
  names: ReadonlyMap<unknown, Named<Definition>>,
  services: Services,
  contracts: readonly Contract[],
): { readonly structure: Structure; readonly thrownDefaults: readonly ThrownDefault[] } {
  const ref: RefOf = (value) => {
    const named = names.get(value);
    return named === undefined ? null : { service: named.service, name: named.name };
  };
  const thrownDefaults: ThrownDefault[] = [];
  const schemaOf = (definition: Definition, shape: Shape): JsonSchema => {
    try {
      return objectSchema(shape);
    } catch (error) {
      thrownDefaults.push({ definition, error });
      return {};
    }
  };
  const references = (shape: Shape) =>
    Object.entries(shape).flatMap(([field, schema]) => {
      const target = refTarget(schema);
      return target === undefined ? [] : [{ field, entity: ref(target) }];
    });
  const structure: Structure = {
    services: [...services].map(([name, s]) => ({
      name,
      external: s.definition.external,
      entities: Object.values(s.definition.entities).flatMap((e) => names.get(e)?.name ?? []),
    })),
    contracts: contracts.map((c) => ({
      service: c.service,
      members: Object.fromEntries(Object.entries(c.members).map(([key, member]) => [key, ref(member)])),
    })),
    definitions: definitions.map(({ service, name, definition: d }): DefinitionStructure => {
      if (d.kind === "entity")
        return {
          kind: d.kind,
          service,
          name,
          key: d.single ? null : d.key,
          fields: Object.keys(d.fields),
          unique: d.single ? [] : [...d.unique],
          references: references(d.fields as Shape),
        };
      if (d.kind === "event")
        return {
          kind: d.kind,
          service,
          name,
          change: d.change,
          entity: d.change === "none" ? null : ref(d.entity),
          // An entity event's payload is made of its entity's fields.
          payload: schemaOf(d.change === "none" ? d : d.entity, d.payload),
        };
      if (d.kind === "command")
        return {
          kind: d.kind,
          service,
          name,
          rejects: d.rejects === undefined ? null : [...d.rejects],
          input: schemaOf(d, d.input),
          output: d.output === undefined ? null : schemaOf(d, d.output),
          emits: d.emits.map(ref),
          references: references(d.input as Shape),
          binds: Object.keys(d.binds),
          requires: Object.keys(d.requires),
        };
      if (d.kind === "query")
        return {
          kind: d.kind,
          service,
          name,
          rejects: d.rejects === undefined ? null : [...d.rejects],
          input: schemaOf(d, d.input),
          output: d.output === undefined ? null : schemaOf(d, d.output),
          requires: Object.keys(d.requires),
        };
      if (d.kind === "automation")
        return {
          kind: d.kind,
          service,
          name,
          receives: ref(Object.values(d.receives)[0]),
          command: ref(Object.values(d.commands)[0]),
          binds: Object.keys(d.binds),
          guard: Object.keys(d.guard),
        };
      const chart = chartOf(d) as ChartSpec;
      return { kind: chart.kind, service, name, ...structureOfChart(chart, ref, (shape) => schemaOf(d, shape)) };
    }),
  };
  return { structure, thrownDefaults };
}

const offerKinds = (offers: StateSpec["offers"]): Record<string, "any" | "listed"> =>
  Object.fromEntries(Object.entries(offers ?? {}).map(([control, o]) => [control, o === any ? "any" : "listed"]));

function structureOfChart(
  chart: ChartSpec,
  ref: RefOf,
  schemaOf: (shape: Shape) => JsonSchema,
): Omit<ChartStructure, "kind" | "service" | "name"> {
  const states: StateStructure[] = [];
  const transitions = (node: StateSpec, source: string | null) =>
    transitionArrays(node).flatMap(({ keys, transitions }) =>
      transitions.map(
        (t, index): TransitionStructure => ({
          source,
          keys: [...keys],
          index,
          target: t.target ?? null,
          guards: Object.keys(t.guard ?? {}),
          reenter: t.reenter ?? null,
        }),
      ),
    );
  const visit = (nodes: Readonly<Record<string, StateSpec>>, parent: StateStructure | undefined): void => {
    for (const [name, node] of Object.entries(nodes)) {
      const activities = [
        ...Object.keys(node.calls ?? {}).map(
          (key): ActivityStructure => ({ keyword: "calls", name: key, definition: ref(chart.queries?.[key]) }),
        ),
        ...Object.keys(node.sends ?? {}).map(
          (key): ActivityStructure => ({ keyword: "sends", name: key, definition: ref(chart.commands[key]) }),
        ),
        ...Object.keys(node.shows ?? {}).map(
          (key): ActivityStructure => ({ keyword: "shows", name: key, definition: ref(chart.queries?.[key]) }),
        ),
        ...Object.entries(node.opens ?? {}).map(
          ([key, opens]): ActivityStructure => ({
            keyword: "opens",
            name: key,
            definition: ref(chart.screens?.[key]),
            modal: opens.modal,
          }),
        ),
      ];
      const state: StateStructure = {
        name,
        path: [...(parent?.path ?? []), name],
        parent: parent?.name ?? null,
        kind: node.type ?? (node.states === undefined ? "atomic" : "compound"),
        initial: node.initial ?? null,
        children: Object.keys(node.states ?? {}),
        offers: offerKinds(node.offers),
        activities,
        transitions: transitions(node, name),
        deadlines: Object.keys(node.after ?? {}),
      };
      states.push(state);
      visit(node.states ?? {}, state);
    }
  };
  visit(chart.states, undefined);
  const byKey = (record: Readonly<Record<string, unknown>> | undefined) =>
    Object.fromEntries(Object.entries(record ?? {}).map(([key, value]) => [key, ref(value)]));
  return {
    initial: chart.initial,
    context: Object.keys(chart.context),
    input: Object.keys(chart.input ?? {}),
    output: Object.keys(chart.output ?? {}),
    requires: Object.keys(chart.requires ?? {}),
    ensures: Object.keys(chart.ensures ?? {}),
    on: transitions({ on: chart.on }, null),
    offers: offerKinds(chart.offers),
    states,
    controls: Object.fromEntries(
      Object.entries(chart.controls ?? {}).map(([name, control]) => [
        name,
        control.payload === undefined ? null : schemaOf(control.payload),
      ]),
    ),
    receives: byKey(chart.receives),
    commands: byKey(chart.commands),
    queries: byKey(chart.queries),
    screens: byKey(chart.screens),
  };
}
