import { z } from "zod";
import type { Malformed } from "../data/malformed.ts";
import { childrenOf, schemaNode } from "../data/schemaNode.ts";
import type { Definition, Named } from "../dsl/definition.ts";
import type { Found } from "./found.ts";
import { declaringEntries, isDefinitionOrService, isPlainObject } from "./schemas.ts";

/** The Zod types whose values JSON cannot hold, after Zod's toJSONSchema; a `transform` has no way back to JSON. */
const unrepresentableTypes = new Set([
  "bigint",
  "symbol",
  "undefined",
  "void",
  "nan",
  "date",
  "map",
  "set",
  "transform",
  "custom",
  "promise",
  "function",
  "file",
]);

type Unrepresentable = { readonly path: readonly string[]; readonly type: string };

/** Walks the JSON side of each schema in `value`: a codec's input, both sides of any other pipe. */
function unrepresentableIn(value: unknown, path: readonly string[], seen: Set<object>): Unrepresentable[] {
  if (typeof value !== "object" || value === null || seen.has(value)) return [];
  seen.add(value);
  if (!(value instanceof z.ZodType)) {
    if (Array.isArray(value)) return value.flatMap((v) => unrepresentableIn(v, path, seen));
    if (!isPlainObject(value) || isDefinitionOrService(value)) return [];
    return Object.entries(value).flatMap(([key, v]) => unrepresentableIn(v, [...path, key], seen));
  }
  const def = value.def as { readonly type: string; readonly in?: z.ZodType; readonly out?: z.ZodType };
  if (unrepresentableTypes.has(def.type)) return [{ path, type: def.type }];
  if (def.type === "pipe")
    return [def.in, ...("reverseTransform" in def ? [] : [def.out])].flatMap((s) => unrepresentableIn(s, path, seen));
  const node = schemaNode(value);
  if (node.type === "object")
    return Object.entries(node.shape).flatMap(([key, s]) => unrepresentableIn(s, [...path, key], seen));
  return childrenOf(node).flatMap((s) => unrepresentableIn(s, path, seen));
}

export function unrepresentableSchemas(
  definitions: readonly Named<Definition>[],
  constants: readonly Named<{ readonly schema: z.ZodObject }>[],
): Found<Malformed>[] {
  return [
    ...definitions.flatMap(({ service, name, place, definition }) => {
      const seen = new Set<object>();
      return declaringEntries(definition)
        .flatMap(([key, value]) => unrepresentableIn(value, [key], seen))
        .map(
          (data): Found<Malformed> => ({
            violation: { kind: "Malformed.unrepresentableSchema", definition: { service, name }, data },
            place,
          }),
        );
    }),
    ...constants.flatMap(({ name, place, definition }) =>
      unrepresentableIn(definition.schema, [], new Set()).map(
        (data): Found<Malformed> => ({
          violation: { kind: "Malformed.unrepresentableSchema", definition: null, data: { name, ...data } },
          place,
        }),
      ),
    ),
  ];
}
