import type { z } from "zod";
import { type Collection, collectionOf, sortsInside } from "../data/collections.ts";
import type { Malformed } from "../data/malformed.ts";
import { childrenOf, schemaNode } from "../data/schemaNode.ts";
import type { Definition, Named } from "../dsl/definition.ts";
import type { Found } from "./found.ts";
import { definitionSchemas, type SchemaAt, schemasIn } from "./schemas.ts";

function collectionsInside(schema: z.ZodType): Collection[] {
  const seen = new Set<z.ZodType>([schema]);
  const found: Collection[] = [];
  const visit = (s: z.ZodType): void => {
    for (const child of childrenOf(schemaNode(s))) {
      if (seen.has(child)) continue;
      seen.add(child);
      const collection = collectionOf(child);
      if (collection !== undefined) found.push(collection);
      visit(child);
    }
  };
  visit(schema);
  return found;
}

function opaqueIn(
  schemas: readonly SchemaAt[],
): { readonly path: readonly string[]; readonly collection: Collection["kind"] }[] {
  const reported = new Set<string>();
  const found: { readonly path: readonly string[]; readonly collection: Collection["kind"] }[] = [];
  for (const { path, schema } of schemas) {
    if (sortsInside(schemaNode(schema))) continue;
    for (const collection of collectionsInside(schema)) {
      const key = JSON.stringify([path, collection.kind]);
      if (reported.has(key)) continue;
      reported.add(key);
      found.push({ path, collection: collection.kind });
    }
  }
  return found;
}

export function opaqueCollections(
  definitions: readonly Named<Definition>[],
  constants: readonly Named<{ readonly schema: z.ZodObject }>[],
): Found<Malformed>[] {
  return [
    ...definitions.flatMap(({ service, name, place, definition }) =>
      opaqueIn(definitionSchemas(definition)).map(
        (data): Found<Malformed> => ({
          violation: { kind: "Malformed.opaqueCollection", definition: { service, name }, data },
          place,
        }),
      ),
    ),
    ...constants.flatMap(({ name, place, definition }) =>
      opaqueIn(schemasIn(definition.schema, [])).map(
        (data): Found<Malformed> => ({
          violation: { kind: "Malformed.opaqueCollection", definition: null, data: { name, ...data } },
          place,
        }),
      ),
    ),
  ];
}
