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
import type { Structure } from "../spec/structure.generated.ts";
import type {
  ActivityStructure,
  ChartStructure,
  DefinitionStructure,
  StateStructure,
  TransitionStructure,
} from "../spec/structure.ts";
import { keyPositions } from "./schemas.ts";

/** Returns the ref of the definition `value`, or throws Unresolved, naming the place `at`, when it is none. */
type RefOf = (value: unknown, at: string) => DefinitionRef;

class Unresolved {
  readonly at: string;
  constructor(at: string) {
    this.at = at;
  }
}

/** The value that a default function threw while a schema that `definition` declares was converted to JSON Schema. */
export interface ThrownDefault {
  readonly definition: Definition;
  readonly error: unknown;
}

/**
 * Returns the one value of an automation's `receives` or `commands`, or undefined for any other count, which only `any`
 * gets past OneKey.
 */
function oneEntry(record: Readonly<Record<string, unknown>>): unknown {
  const values = Object.values(record);
  return values.length === 1 ? values[0] : undefined;
}

/**
 * The structure, or, when a definition names a value that is no definition of the spec, where it does. Such a value
 * passes the types only through a value of type `any` or an export that the spec lacks, which check reports as
 * Restricted.any or Malformed.unexportedDefinition.
 */
export type StructureOf =
  | { readonly structure: Structure; readonly thrownDefaults: readonly ThrownDefault[] }
  | { readonly structure: undefined; readonly unresolved: string };

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
): StructureOf {
  const nameOf = (value: unknown): DefinitionRef | undefined => {
    const named = names.get(value);
    return named === undefined ? undefined : { service: named.service, name: named.name };
  };
  const ref: RefOf = (value, at) => {
    const found = nameOf(value);
    if (found === undefined) throw new Unresolved(at);
    return found;
  };
  try {
    return structureWith(definitions, services, contracts, ref, nameOf);
  } catch (error) {
    if (error instanceof Unresolved) return { structure: undefined, unresolved: error.at };
    throw error;
  }
}

function structureWith(
  definitions: readonly Named<Definition>[],
  services: Services,
  contracts: readonly Contract[],
  ref: RefOf,
  nameOf: (value: unknown) => DefinitionRef | undefined,
): { readonly structure: Structure; readonly thrownDefaults: readonly ThrownDefault[] } {
  const thrownDefaults: ThrownDefault[] = [];
  const schemaOf = (definition: Definition, shape: Shape): JsonSchema => {
    try {
      return objectSchema(shape);
    } catch (error) {
      thrownDefaults.push({ definition, error });
      return {};
    }
  };
  const references = (shape: Shape, at: string) =>
    Object.entries(shape).flatMap(([field, schema]) => {
      const target = refTarget(schema);
      return target === undefined ? [] : [{ field, entity: ref(target, `${at} ref field ${field}`) }];
    });
  const structure: Structure = {
    services: [...services].map(([name, s]) => ({
      name,
      external: s.definition.external,
      entities: Object.values(s.definition.entities).flatMap((e) => nameOf(e)?.name ?? []),
    })),
    contracts: contracts.map((c) => ({
      service: c.service,
      members: Object.fromEntries(Object.entries(c.members).map(([key, member]) => [key, nameOf(member) ?? null])),
    })),
    definitions: definitions.map(({ service, name, definition: d }): DefinitionStructure => {
      const at = `the ${d.kind} ${service}.${name}`;
      if (d.kind === "entity")
        return {
          kind: d.kind,
          service,
          name,
          key: d.single ? null : d.key,
          fields: Object.keys(d.fields),
          unique: d.single ? [] : [...d.unique],
          references: references(d.fields as Shape, at),
          keys: keysOf(d.fields as Shape, ref, at),
        };
      if (d.kind === "event")
        return {
          kind: d.kind,
          service,
          name,
          change: d.change === "none" ? null : { kind: d.change, entity: ref(d.entity, `${at} entity`) },
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
          emits: d.emits.map((e, i) => ref(e, `${at} emits ${i}`)),
          references: references(d.input as Shape, at),
          binds: Object.keys(d.binds),
          requires: Object.keys(d.requires),
          ensures: Object.keys(d.ensures),
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
          ensures: Object.keys(d.ensures),
        };
      if (d.kind === "automation")
        return {
          kind: d.kind,
          service,
          name,
          receives: ref(oneEntry(d.receives), `${at} receives`),
          command: ref(oneEntry(d.commands), `${at} commands`),
          binds: Object.keys(d.binds),
          guard: Object.keys(d.guard),
        };
      const chart = chartOf(d) as ChartSpec;
      return {
        kind: chart.kind,
        service,
        name,
        ...structureOfChart(
          chart,
          (value, place) => ref(value, `${at} ${place}`),
          (shape) => schemaOf(d, shape),
        ),
      };
    }),
  };
  return { structure, thrownDefaults };
}

const keysOf = (shape: Shape, ref: RefOf, at: string) =>
  keyPositions(shape).map(({ path, entity }) => ({
    path: [...path],
    entity: ref(entity, `${at} key ${path.join(".")}`),
  }));

const offerKinds = (offers: StateSpec["offers"]): Record<string, StateStructure["offers"][string]> =>
  Object.fromEntries(Object.entries(offers ?? {}).map(([control, o]) => [control, o === any ? "any" : "listed"]));

function structureOfChart(
  chart: ChartSpec,
  ref: RefOf,
  schemaOf: (shape: Shape) => JsonSchema,
): Omit<ChartStructure, "kind" | "service" | "name"> {
  const states: StateStructure[] = [];
  const transitions = (node: StateSpec, source: string | null) =>
    transitionArrays(node).flatMap(({ trigger, transitions }) =>
      transitions.map(
        (t, index): TransitionStructure => ({
          source,
          trigger,
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
          (key): ActivityStructure => ({
            keyword: "calls",
            name: key,
            definition: ref(chart.queries?.[key], `state ${name} calls ${key}`),
          }),
        ),
        ...Object.keys(node.sends ?? {}).map(
          (key): ActivityStructure => ({
            keyword: "sends",
            name: key,
            definition: ref(chart.commands[key], `state ${name} sends ${key}`),
          }),
        ),
        ...Object.keys(node.shows ?? {}).map(
          (key): ActivityStructure => ({
            keyword: "shows",
            name: key,
            definition: ref(chart.queries?.[key], `state ${name} shows ${key}`),
          }),
        ),
        ...Object.entries(node.opens ?? {}).map(
          ([key, opens]): ActivityStructure => ({
            keyword: "opens",
            name: key,
            definition: ref(chart.screens?.[key], `state ${name} opens ${key}`),
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
        itemKeys: keysOf(node.key ?? {}, ref, `state ${name}`),
        contextKeys: keysOf(node.context ?? {}, ref, `state ${name} context`),
        hasParameters: node.held !== undefined,
        heldKeys: keysOf(node.held ?? {}, ref, `state ${name} held`),
      };
      states.push(state);
      visit(node.states ?? {}, state);
    }
  };
  visit(chart.states, undefined);
  const byKey = (keyword: string, record: Readonly<Record<string, unknown>> | undefined) =>
    Object.fromEntries(Object.entries(record ?? {}).map(([key, value]) => [key, ref(value, `${keyword} ${key}`)]));
  return {
    initial: chart.initial,
    context: Object.keys(chart.context),
    contextKeys: keysOf(chart.context, ref, "context"),
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
    receives: byKey("receives", chart.receives),
    commands: byKey("commands", chart.commands),
    queries: byKey("queries", chart.queries),
    screens: byKey("screens", chart.screens),
  };
}
