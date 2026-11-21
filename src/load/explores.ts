import type { z } from "zod";
import { expectFound } from "../data/internalError.ts";
import { partAt, writtenAs } from "../data/jsonSchema.ts";
import type { Malformed } from "../data/malformed.ts";
import type { SchemaStep } from "../data/schema.generated.ts";
import { schemaNode } from "../data/schemaNode.ts";
import { type Json, objectOf, sameJson } from "../data/values.ts";
import { type Definition, type Named, type Place, shapeIn } from "../dsl/definition.ts";
import { keyTarget } from "../dsl/entity.ts";
import type { Domain, Explore } from "../dsl/explore.ts";
import { moveSchemas, rootTree } from "../spec/domains.ts";
import type { Structure } from "../spec/structure.generated.ts";
import { type DomainStructure, type ExploreStructure, schemaOwner } from "../spec/structure.ts";
import type { Found } from "./found.ts";

const isJson = (value: unknown): value is Json =>
  value === null ||
  typeof value === "string" ||
  typeof value === "boolean" ||
  (typeof value === "number" && Number.isFinite(value)) ||
  (Array.isArray(value) && value.every(isJson)) ||
  (typeof value === "object" &&
    Object.getPrototypeOf(value) === Object.prototype &&
    Object.values(value as object).every(isJson));

/** A domain value that is not JSON or that its schema rejects, refinements included, is Malformed.domainValue. */
export function domainValues(service: string, written: Explore, place: Place): Found<Malformed>[] {
  return written.domains.flatMap((d, domain) =>
    d.values.flatMap((value, index): Found<Malformed>[] => {
      let accepted: boolean;
      try {
        accepted = isJson(value) && d.schema.safeParse(value).success;
      } catch {
        accepted = false;
      }
      return accepted
        ? []
        : [
            {
              violation: { kind: "Malformed.domainValue", definition: null, data: { service, domain, value: index } },
              place,
            },
          ];
    }),
  );
}

/**
 * The entity whose key the node that `schema` is written as holds, or undefined. A nullable node is a union that holds
 * the key in one option and null in the other, and the key option is the node that a key domain names.
 */
function keyAt(schema: z.ZodType): unknown {
  const written = writtenAs(schema);
  if (schemaNode(written.at(-1) ?? schema).type === "nullable") return undefined;
  return written.map(keyTarget).find((target) => target !== undefined);
}

/** Whether `d` names the node whose Zod part is `part`: the schema written there, or a key of the same entity. */
function names(d: Domain, part: z.ZodType): boolean {
  const target = keyAt(d.schema);
  return writtenAs(part).includes(d.schema) || (target !== undefined && keyAt(part) === target);
}

/**
 * The Zod part of `root` at `path` of its JSON Schema. Zod writes a nullable of a plain type as a list of types, and any
 * other list of types once per type of one schema, whose option is that schema itself.
 */
const partFor = (root: z.ZodType, path: readonly SchemaStep[]): z.ZodType =>
  path.reduce((at, step) => {
    const node = schemaNode(writtenAs(at).at(-1) ?? at).type;
    return step.kind === "option" && node !== "union" && node !== "nullable" ? at : partAt(at, [step]);
  }, root);

const isPrefix = (outer: readonly SchemaStep[], inner: readonly SchemaStep[]): boolean =>
  outer.length < inner.length && outer.every((step, i) => sameJson(step, inner[i] ?? null));

/**
 * The explore of `service` with each domain of `written` at the nodes that it names, among the nodes that treeOf reads
 * of the schemas that the service's moves may carry, with Malformed.unusedDomain and overlappingDomain.
 */
export function placeDomains(
  structure: Structure,
  definitions: readonly Named<Definition>[],
  service: string,
  written: Explore,
  place: Place,
): { readonly explore: ExploreStructure; readonly malformed: readonly Found<Malformed>[] } {
  const domains: DomainStructure[] = [];
  const used = new Set<number>();
  const overlapping = new Map<string, number[]>();
  for (const [schema, json] of moveSchemas(structure, service)) {
    const owner = schemaOwner(schema);
    const named = expectFound(
      `definition ${owner.service}.${owner.name}`,
      definitions.find((d) => d.service === owner.service && d.name === owner.name),
    );
    const root = objectOf(shapeIn(named.definition, schema));
    const nodes = new Map<string, { readonly path: readonly SchemaStep[]; readonly naming: readonly number[] }>();
    rootTree((path) => {
      const part = partFor(root, path);
      const naming = written.domains.flatMap((d, i) => (names(d, part) ? [i] : []));
      if (naming.length > 0) nodes.set(JSON.stringify(path), { path: [...path], naming });
      return undefined;
    }, json);
    for (const { path, naming } of nodes.values()) {
      for (const i of naming) used.add(i);
      const outer = [...nodes.values()].filter((n) => isPrefix(n.path, path)).flatMap((n) => n.naming);
      const covering = [...new Set([...outer, ...naming])].sort((a, b) => a - b);
      if (covering.length > 1) overlapping.set(covering.join(), covering);
      if (outer.length > 0) continue;
      const first = expectFound("a naming domain", naming[0]);
      const values = expectFound(`domain ${first}`, written.domains[first]).values as Json[];
      domains.push({ schema, path, values });
    }
  }
  const malformed = [
    ...written.domains.flatMap((_, domain): Malformed[] =>
      used.has(domain) ? [] : [{ kind: "Malformed.unusedDomain", definition: null, data: { service, domain } }],
    ),
    ...[...overlapping.values()].map(
      (naming): Malformed => ({
        kind: "Malformed.overlappingDomain",
        definition: null,
        data: { service, domains: naming },
      }),
    ),
  ].map((violation) => ({ violation, place }));
  return { explore: { service, depth: written.depth, domains }, malformed };
}
