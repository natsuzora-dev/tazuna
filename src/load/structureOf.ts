import { defaultRow, encoded, sortCollections } from "../data/collections.ts";
import { type DefinitionRef, sameRef } from "../data/definitionRef.ts";
import { type JsonSchema, jsonSchema, objectSchema } from "../data/jsonSchema.ts";
import type { Expected, Malformed } from "../data/malformed.ts";
import { type Shape, sameJson, strictObjectOf } from "../data/values.ts";
import { thrown, type ViolationError, zodError } from "../data/violation.ts";
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
import type { DeadlineTime, StateType, Structure } from "../spec/structure.generated.ts";
import type {
  ActivityStructure,
  ChartStructure,
  DefinitionStructure,
  StateStructure,
  TransitionStructure,
} from "../spec/structure.ts";
import type { Found } from "./found.ts";
import { keyPositions } from "./schemas.ts";

type Path = readonly (string | number)[];

/** Returns the ref of the definition `value` at `path`, which must be `expected`. */
type RefOf = (value: unknown, path: Path, expected: Expected) => DefinitionRef;

/** Stands where a definition names nothing it can resolve, in a structure that structureOf then drops. */
const unresolved: DefinitionRef = { service: "", name: "" };

const isExpected = (definition: Definition, expected: Expected): boolean =>
  expected === "keyedEntity" ? definition.kind === "entity" && !definition.single : definition.kind === expected;

/** Returns the one value of an automation's `receives` or `commands`; OneKey lets only `any` give another count. */
function oneEntry(record: Readonly<Record<string, unknown>>): unknown {
  const values = Object.values(record);
  return values.length === 1 ? values[0] : undefined;
}

/**
 * The structure, or what was found on the way where the structure would hold a placeholder (Malformed.unresolvedReference,
 * defaultSchema). A value that no export names is left to unexportedDefinitions and owners, which report it; `unnamed`
 * lists where, so that load can tell when neither did.
 */
export type StructureOf =
  | { readonly kind: "built"; readonly structure: Omit<Structure, "explores"> }
  | { readonly kind: "found"; readonly malformed: readonly Found<Malformed>[]; readonly unnamed: readonly string[] };

/**
 * Returns the error of the defaults of a shape whose every field gets its value from its default: Zod's issues, or what
 * a default function or a refinement threw. Zod does not validate default values itself, so they are encoded, sorted and
 * parsed as the run checks a value that spec code made.
 */
function defaultsError(shape: Shape): ViolationError | undefined {
  try {
    const object = strictObjectOf(shape);
    const json = encoded(object, defaultRow(shape));
    if ("error" in json) return zodError(json.error.issues);
    const parsed = object.safeParse(sortCollections(jsonSchema(object), json.encoded));
    return parsed.success ? undefined : zodError(parsed.error.issues);
  } catch (error) {
    return thrown(error);
  }
}

/** Computes state trees and definition refs, which every other part reads from this JSON. */
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
  const malformed: Found<Malformed>[] = [];
  const unnamed: string[] = [];
  const defaultSchema = (owner: Definition, map: string | undefined, error: ViolationError): void => {
    const named = names.get(owner);
    if (named === undefined) return;
    const definition = { service: named.service, name: named.name };
    const violation: Malformed =
      map === undefined
        ? { kind: "Malformed.defaultSchema", definition, data: {} }
        : { kind: "Malformed.defaultSchema", definition, data: { map } };
    const found = malformed.some(
      ({ violation: v }) =>
        v.kind === violation.kind && sameRef(v.definition, definition) && sameJson(v.data, violation.data),
    );
    if (!found) malformed.push({ violation, place: named.place, error });
  };
  const structure: Omit<Structure, "explores"> = {
    services: [...services].map(([name, s]) => ({
      name,
      external: s.definition.external,
      entities: Object.entries(s.definition.entities).flatMap(([key, e]) => {
        const found = nameOf(e);
        if (found === undefined) unnamed.push(`the service ${name} entities ${key}`);
        return found === undefined ? [] : [found.name];
      }),
    })),
    contracts: contracts.map((c) => ({
      service: c.service,
      members: Object.fromEntries(Object.entries(c.members).map(([key, member]) => [key, nameOf(member) ?? null])),
    })),
    definitions: definitions.map((named) => {
      const { service, name, place, definition } = named;
      const ref: RefOf = (value, path, expected) => {
        const found = names.get(value);
        if (found !== undefined && isExpected(found.definition, expected))
          return { service: found.service, name: found.name };
        if (value === undefined || found !== undefined)
          malformed.push({
            violation: {
              kind: "Malformed.unresolvedReference",
              definition: { service, name },
              data: { path: [...path], expected },
            },
            place,
          });
        else unnamed.push(`the ${definition.kind} ${service}.${name} at ${path.join(".")}`);
        return unresolved;
      };
      const schemaOf = (owner: Definition, shape: Shape, map?: string): JsonSchema => {
        try {
          return objectSchema(shape);
        } catch (error) {
          defaultSchema(owner, map, thrown(error));
          return {};
        }
      };
      const defaultsOf = (owner: Definition, shape: Shape, map?: string): void => {
        const error = defaultsError(shape);
        if (error !== undefined) defaultSchema(owner, map, error);
      };
      const unreadableDeadline = (path: Path) =>
        malformed.push({
          violation: { kind: "Malformed.unreadableDeadline", definition: { service, name }, data: { path: [...path] } },
          place,
        });
      return definitionStructure(named, ref, schemaOf, defaultsOf, unreadableDeadline);
    }),
  };
  return malformed.length > 0 || unnamed.length > 0
    ? { kind: "found", malformed, unnamed }
    : { kind: "built", structure };
}

function definitionStructure(
  { service, name, definition: d }: Named<Definition>,
  ref: RefOf,
  schemaOf: (owner: Definition, shape: Shape, map?: string) => JsonSchema,
  defaultsOf: (owner: Definition, shape: Shape, map?: string) => void,
  unreadableDeadline: (path: Path) => void,
): DefinitionStructure {
  const references = (shape: Shape, key: string) =>
    Object.entries(shape).flatMap(([field, schema]) => {
      const target = refTarget(schema);
      return target === undefined ? [] : [{ field, entity: ref(target, [key, field], "keyedEntity") }];
    });
  if (d.kind === "entity") {
    const fields = schemaOf(d, d.fields as Shape);
    if (d.single) defaultsOf(d, d.fields as Shape);
    return {
      kind: d.kind,
      service,
      name,
      key: d.single ? null : d.key,
      fields,
      unique: d.single ? [] : [...d.unique],
      references: references(d.fields as Shape, "fields"),
      keys: keysOf(d.fields as Shape, ref, ["fields"]),
    };
  }
  if (d.kind === "event")
    return {
      kind: d.kind,
      service,
      name,
      change:
        d.change === "none"
          ? null
          : { kind: d.change, entity: ref(d.entity, ["entity"], d.change === "update" ? "entity" : "keyedEntity") },
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
      emits: d.emits.map((e, i) => ref(e, ["emits", i], "event")),
      references: references(d.input as Shape, "input"),
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
      receives: ref(oneEntry(d.receives), ["receives"], "event"),
      command: ref(oneEntry(d.commands), ["commands"], "command"),
      binds: Object.keys(d.binds),
      guard: Object.keys(d.guard),
      onRejected: d.onRejected !== undefined,
    };
  const chart = chartOf(d) as ChartSpec;
  return {
    kind: chart.kind,
    service,
    name,
    ...structureOfChart(
      chart,
      ref,
      (shape, map) => schemaOf(d, shape, map),
      (shape, map) => defaultsOf(d, shape, map),
      unreadableDeadline,
    ),
  };
}

/**
 * Returns how the time of the deadline `d` is computed, with its delay in milliseconds, or null when the delay is no
 * safe integer. A deadline with both a delay and an `at` or neither, which only `any` gets past the types, is
 * `unreadable`.
 */
function deadlineTimeOf(d: { readonly delay?: unknown; readonly at?: unknown }, unreadable: () => void): DeadlineTime {
  if ((d.at === undefined) === (d.delay === undefined)) {
    unreadable();
    return { kind: "delay", ms: null };
  }
  if (d.delay === undefined) return { kind: "at" };
  return { kind: "delay", ms: Number.isSafeInteger(d.delay) ? (d.delay as number) : null };
}

const keysOf = (shape: Shape, ref: RefOf, at: Path) =>
  keyPositions(shape).map(({ path, entity }) => ({
    path: [...path],
    entity: ref(entity, [...at, ...path], "keyedEntity"),
  }));

const offerKinds = (offers: StateSpec["offers"]): Record<string, StateStructure["offers"][string]> =>
  Object.fromEntries(Object.entries(offers ?? {}).map(([control, o]) => [control, o === any ? "any" : "listed"]));

function structureOfChart(
  chart: ChartSpec,
  ref: RefOf,
  schemaOf: (shape: Shape, map?: string) => JsonSchema,
  defaultsOf: (shape: Shape, map: string) => void,
  unreadableDeadline: (path: Path) => void,
): Omit<ChartStructure, "kind" | "service" | "name"> {
  const byKey = (keyword: string, record: Readonly<Record<string, unknown>> | undefined, expected: Expected) =>
    Object.fromEntries(Object.entries(record ?? {}).map(([key, value]) => [key, ref(value, [keyword, key], expected)]));
  const receives = byKey("receives", chart.receives, "event");
  const commands = byKey("commands", chart.commands, "command");
  const queries = byKey("queries", chart.queries, "query");
  const screens = byKey("screens", chart.screens, "screen");
  /** The ref under `key` of the chart's `refs`, which the activity at `path` names; a missing key is reported there. */
  const named = (refs: Readonly<Record<string, DefinitionRef>>, key: string, path: Path, expected: Expected) =>
    refs[key] ?? ref(undefined, path, expected);
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
  const visit = (
    nodes: Readonly<Record<string, StateSpec>>,
    parent: StateStructure | undefined,
    within: Path,
  ): void => {
    for (const [name, node] of Object.entries(nodes)) {
      const at = [...within, "states", name];
      const activities = [
        ...Object.entries(node.calls ?? {}).map(
          ([key, call]): ActivityStructure => ({
            keyword: "calls",
            name: key,
            definition: named(queries, key, [...at, "calls", key], "query"),
            onRejected: call.onRejected !== undefined,
          }),
        ),
        ...Object.entries(node.sends ?? {}).map(
          ([key, send]): ActivityStructure => ({
            keyword: "sends",
            name: key,
            definition: named(commands, key, [...at, "sends", key], "command"),
            onRejected: send.onRejected !== undefined,
          }),
        ),
        ...Object.keys(node.shows ?? {}).map(
          (key): ActivityStructure => ({
            keyword: "shows",
            name: key,
            definition: named(queries, key, [...at, "shows", key], "query"),
          }),
        ),
        ...Object.entries(node.opens ?? {}).map(
          ([key, opens]): ActivityStructure => ({
            keyword: "opens",
            name: key,
            definition: named(screens, key, [...at, "opens", key], "screen"),
            modal: opens.modal,
          }),
        ),
      ];
      const type = ((): StateType => {
        if (node.type !== "map") return { kind: node.type ?? "plain" };
        const context = schemaOf(node.context ?? {}, name);
        defaultsOf(node.context ?? {}, name);
        return {
          kind: "map",
          map: {
            key: schemaOf(node.key),
            context,
            itemKeys: keysOf(node.key, ref, [...at, "key"]),
            contextKeys: keysOf(node.context ?? {}, ref, [...at, "context"]),
          },
        };
      })();
      const state: StateStructure = {
        name,
        path: [...(parent?.path ?? []), name],
        parent: parent?.name ?? null,
        ...type,
        initial: node.initial ?? null,
        children: Object.keys(node.states ?? {}),
        offers: offerKinds(node.offers),
        activities,
        transitions: transitions(node, name),
        deadlines: Object.entries(node.after ?? {}).map(([deadline, d]) => ({
          name: deadline,
          ...deadlineTimeOf(d, () => unreadableDeadline([...at, "after", deadline])),
        })),
        held:
          node.held === undefined
            ? null
            : { schema: schemaOf(node.held), keys: keysOf(node.held, ref, [...at, "held"]) },
      };
      states.push(state);
      visit(node.states ?? {}, state, at);
    }
  };
  visit(chart.states, undefined, []);
  return {
    initial: chart.initial,
    context: schemaOf(chart.context),
    contextKeys: keysOf(chart.context, ref, ["context"]),
    input: schemaOf(chart.input ?? {}),
    output: schemaOf(chart.output ?? {}),
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
    receives,
    commands,
    queries,
    screens,
  };
}
