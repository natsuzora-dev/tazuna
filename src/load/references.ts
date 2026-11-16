import type { z } from "zod";
import type { Malformed } from "../data/malformed.ts";
import { chartOf } from "../dsl/chart.ts";
import {
  type ChartSpec,
  type Contract,
  type Definition,
  isDefinition,
  type Named,
  type Place,
  type ServiceDefinition,
} from "../dsl/definition.ts";
import { refTarget } from "../dsl/entity.ts";
import type { Scenario } from "../dsl/scenario.ts";
import type { Found } from "./found.ts";
import { definitionSchemas, type SchemaAt, schemasIn } from "./schemas.ts";

interface Reference {
  readonly path: readonly (string | number)[];
  readonly target: unknown;
}

const entries = (key: string, record: Readonly<Record<string, unknown>> | undefined): Reference[] =>
  Object.entries(record ?? {}).map(([k, target]) => ({ path: [key, k], target }));

const elements = (key: string, array: readonly unknown[] | undefined): Reference[] =>
  (array ?? []).map((target, i) => ({ path: [key, i], target }));

const chartReferences = (chart: ChartSpec): Reference[] => [
  ...entries("receives", chart.receives),
  ...entries("commands", chart.commands),
  ...entries("queries", chart.queries),
  ...entries("screens", chart.screens),
];

/**
 * Returns the references in `schemas`, each counted once: a ref() and the nullable or default around it are found on
 * the same path.
 */
const schemaReferences = (schemas: readonly SchemaAt[]): Reference[] =>
  schemas.flatMap(({ path, schema }, i) => {
    const target = refTarget(schema);
    const counted = schemas
      .slice(0, i)
      .some((s) => refTarget(s.schema) === target && JSON.stringify(s.path) === JSON.stringify(path));
    return target === undefined || counted ? [] : [{ path, target }];
  });

function nonSchemaReferences(definition: Definition): Reference[] {
  switch (definition.kind) {
    case "entity":
    case "query":
      return [];
    case "event":
      return definition.change === "none" ? [] : [{ path: ["entity"], target: definition.entity }];
    case "command":
      return elements("emits", definition.emits);
    case "automation":
      return [...entries("receives", definition.receives), ...entries("commands", definition.commands)];
    case "machine":
    case "screen":
      return chartReferences(chartOf(definition) as ChartSpec);
  }
}

const definitionReferences = (definition: Definition): Reference[] => [
  ...nonSchemaReferences(definition),
  ...schemaReferences(definitionSchemas(definition)),
];

function inputReferences(input: Scenario["inputs"][number], i: number): Reference[] {
  const field = (role: string, target: unknown): Reference => ({ path: ["inputs", i, role], target });
  switch (input.type) {
    case "elsewhere":
    case "from":
      return inputReferences(input.input, i).map((r) => ({ ...r, path: ["inputs", i, "input", ...r.path.slice(2)] }));
    case "at":
    case "unsubscribe":
    case "restart":
      return [];
    case "command":
      return [field("command", input.command)];
    case "query":
    case "subscribe":
      return [field("query", input.query)];
    case "event":
      return [field("event", input.event)];
    case "operation":
    case "unacceptedOperation":
      return [field("screen", input.screen)];
    case "answer":
      return [field("sender", input.sender), field("target", input.target)];
  }
}

/**
 * Returns the references of definitions, scenarios, service definers, `constants()` calls, and contracts to definition
 * objects that no export of the spec names. A reference to an exported definition that no service owns is left to
 * owners, which reports the cause. A definer is read under the first folder whose service it is, as owners names it.
 */
export function unexportedDefinitions(
  definitions: readonly Named<Definition>[],
  scenarios: readonly Named<Scenario>[],
  services: ReadonlyMap<string, { readonly definition: ServiceDefinition; readonly place: Place }>,
  contracts: readonly Contract[],
  constants: readonly Named<{ readonly schema: z.ZodObject }>[],
  exported: ReadonlySet<unknown>,
): Found<Malformed>[] {
  const unexported = (references: readonly Reference[]) => references.filter((r) => !exported.has(r.target));
  const referredBy = ({ service, name, place }: Omit<Named<unknown>, "definition">, references: readonly Reference[]) =>
    unexported(references).map(
      ({ path }): Found<Malformed> => ({
        violation: { kind: "Malformed.unexportedDefinition", definition: { service, name }, data: { path } },
        place,
      }),
    );
  const definers = [...services].filter(
    ([, s], i, all) => all.findIndex(([, t]) => t.definition === s.definition) === i,
  );
  return [
    ...definitions.flatMap((d) => referredBy(d, definitionReferences(d.definition))),
    ...scenarios.flatMap((s) => referredBy(s, s.definition.inputs.flatMap(inputReferences))),
    ...definers.flatMap(([service, { definition, place }]) =>
      unexported(entries("entities", definition.entities)).map(
        ({ path }): Found<Malformed> => ({
          violation: { kind: "Malformed.unexportedDefinition", definition: null, data: { service, path } },
          place,
        }),
      ),
    ),
    ...constants.flatMap(({ name, place, definition }) =>
      unexported(schemaReferences(schemasIn(definition.schema, []))).map(
        ({ path }): Found<Malformed> => ({
          violation: { kind: "Malformed.unexportedDefinition", definition: null, data: { name, path } },
          place,
        }),
      ),
    ),
    ...contracts.flatMap(({ service, place, members }) =>
      Object.entries(members)
        .filter(([key, member]) =>
          isDefinition(member)
            ? !exported.has(member)
            : unexported(schemaReferences(schemasIn(member, [key]))).length > 0,
        )
        .map(
          ([key]): Found<Malformed> => ({
            violation: { kind: "Malformed.unexportedDefinition", definition: null, data: { contract: service, key } },
            place,
          }),
        ),
    ),
  ];
}
